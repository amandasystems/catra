package uuverifiers.parikh_theory

import ap.basetypes.IdealInt
import ap.parser._
import ap.proof.goal.Goal
import ap.proof.theoryPlugins.Plugin
import ap.terfor.TerForConvenience._
import ap.terfor.preds.Atom
import ap.terfor.conjunctions.Conjunction
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.{Formula, TermOrder}
import ap.theories._
import EdgeWrapper._
import ap.parser.IExpression.Predicate

// TODO write a LengthCounting mixin which interns one term for length and
// yields that for each transition
// TODO work through terminology. Why do we use "register values"?
// TODO use [M <: Monoid with Abelian, A <: Automaton]
// FIXME: this is a constructor for a theory, it never registers itself!

/**
 * The Parikh Theory enforces Parikh Image membership modulo a morphism to a
 * commutative monoid. The most straightforward example is string length, with
 * an automaton representing the possible strings.
 */
trait ParikhTheory[A <: Automaton]
    extends Theory
    with NoFunctions
    with NoAxioms
    with Tracing
    with Complete {

  val aut: A

  /**
   * This method provides the "modulo" aspect by performing the translation
   * from a transition (usually really the transition's label) to a commutative
   * monoid (M).
   *
   * For example length-counting would map all transitions representing a
   * single character (typically all transitions) to 1.
   */
  def toMonoid(a: aut.Transition): Seq[LinearCombination]

  lazy private val autGraph = aut.toGraph
  lazy private val cycles = trace("cycles")(autGraph.simpleCycles)

  // This describes the status of a transition in the current model
  protected sealed trait TransitionSelected {
    def definitelyAbsent = false
    def isUnknown = false
  }

  object TransitionSelected {
    case object Present extends TransitionSelected
    case object Absent extends TransitionSelected {
      override def definitelyAbsent = true
    }
    case object Unknown extends TransitionSelected {
      override def isUnknown = true
    }
  }

  private object TransitionSplitter extends PredicateHandlingProcedure {
    override val procedurePredicate = predicate
    override def handlePredicateInstance(
        goal: Goal
    )(predicateAtom: Atom): Seq[Plugin.Action] = trace("TransitionSplitter") {
      implicit val _ = goal.order

      val transitionTerms = trace("transitionTerms") {
        predicateAtom.take(aut.transitions.size)
      }

      val unknownTransitions = trace("unknownTransitions") {
        transitionTerms filter (
            t => transitionStatusFromTerm(goal, t).isUnknown
        )
      }

      trace("unknownActions") {
        def transitionToSplit(transitionTerm: LinearCombination) =
          Plugin.AxiomSplit(
            Seq(),
            Seq(transitionTerm <= 0, transitionTerm > 0)
              .map(eq => (conj(eq), Seq())),
            ParikhTheory.this
          )

        val splittingActions = trace("splittingActions") {
          unknownTransitions
            .map(transitionToSplit(_))
            .toSeq
        }

        Seq(splittingActions.head)

      }
    }
  }

  private object ConnectednessPropagator
      extends Plugin
      with PredicateHandlingProcedure
      with NoAxiomGeneration {
    // Handle a specific predicate instance for a proof goal, returning the
    // resulting plugin actions.
    override val procedurePredicate = predicate
    override def handlePredicateInstance(
        goal: Goal
    )(predicateAtom: Atom): Seq[Plugin.Action] =
      trace("ConnectednessPropagator") {
        implicit val _ = goal.order

        // try { throw new Exception() } catch {case e => e.printStackTrace}

        val transitionTerms = predicateAtom.take(aut.transitions.size)

        val transitionToTerm =
          trace("transitionToTerm")(
            aut.transitions.to.zip(transitionTerms).toMap
          )

        // FIXME this is highly inefficient repeat work and should be factored
        // out.
        val isSubsumed = trace("isSubsumed") {
          !(transitionTerms exists (
              t => transitionStatusFromTerm(goal, t).isUnknown
          ))

        }

        if (isSubsumed) {
          return Seq(Plugin.RemoveFacts(predicateAtom))
        }

        val splittingActions = trace("splittingActions") {
          goalState(goal) match {
            case Plugin.GoalState.Final => TransitionSplitter.handleGoal(goal)
            case _                      => List(Plugin.ScheduleTask(TransitionSplitter, 0))
          }
        }

        // TODO: we don't care about splitting edges that cannot possibly cause a
        // disconnect; i.e. *we only care* about critical edges on the path to
        // some cycle that can still appear (i.e. wose edges are not
        // known-deselected).

        // constrain any terms associated with a transition from a
        // *known* unreachable state to be = 0 ("not used").
        val unreachableActions = trace("unreachableActions") {
          val deadTransitions = trace("deadTransitions") {
            aut.transitions
              .filter(
                t => termMeansDefinitelyAbsent(goal, transitionToTerm(t))
              )
              .to[Set]
          }

          val unreachableConstraints =
            conj(
              autGraph
                .dropEdges(deadTransitions)
                .unreachableFrom(aut.initialState)
                .flatMap(
                  autGraph.transitionsFrom(_).map(transitionToTerm(_) === 0)
                )
            )

          if (unreachableConstraints.isTrue) Seq()
          else
            Seq(
              Plugin.AddAxiom(
                Seq(predicateAtom),
                unreachableConstraints,
                ParikhTheory.this
              )
            )
        }

        unreachableActions ++ splittingActions
      }
  }

  // FIXME: total deterministisk ordning på edges!
  // FIXME: name the predicate!
  // FIXME: add back the registers
  lazy private val predicate =
    new Predicate(
      s"pa-${aut.hashCode}",
      // the one here is the y parameter of the paper. If we have
      // register/symbol automata, this would be the number of registers. As it
      // stands, we just have one.
      autGraph.edges.size + 1
    )

  lazy val predicates: Seq[ap.parser.IExpression.Predicate] = List(predicate)

  override def preprocess(f: Conjunction, order: TermOrder): Conjunction = {
    implicit val newOrder = order

    def asManyIncomingAsOutgoing(
        transitionAndVar: Seq[(autGraph.Edge, LinearCombination)]
    ): Formula = {
      def asStateFlowSum(
          stateTerms: Seq[(aut.State, (IdealInt, LinearCombination))]
      ) = {
        val (state, _) = stateTerms.head
        val isInitial =
          (if (state == aut.initialState) LinearCombination.ONE
           else LinearCombination.ZERO)
        (state, sum(stateTerms.unzip._2 ++ List((IdealInt.ONE, isInitial))))
      }

      trace("Flow equations") {
        conj(
          transitionAndVar
            .filter(!_._1.isSelfEdge)
            .flatMap {
              case ((from, _, to), transitionVar) =>
                List(
                  (to, (IdealInt.ONE, transitionVar)),
                  (from, (IdealInt.MINUS_ONE, transitionVar))
                )
            }
            .to
            .groupBy(_._1)
            .values
            .map(asStateFlowSum)
            .map {
              case (state, flowSum) =>
                if (aut isAccept state) flowSum >= 0 else flowSum === 0
            }
        )
      }
    }

    /**
     *  This expresses the mapping between the monoid values and the transition
     *  variables. It is the y = Sum t : transitions tVar(t) * h(t), for both
     *  the h-values and y vectors.
     *
     *  TODO: How do we express that this multiplication happens on the
     *  monoid's multiplication?
     */
    def registerValuesReachable(
        registerVars: Seq[LinearCombination],
        transitionAndVar: Seq[(autGraph.Edge, LinearCombination)]
    ): Formula = {
      trace("Register equations") {
        // This is just a starting vector of the same dimension as the monoid
        // values.
        val startVectorSum: Seq[LinearCombination] =
          Seq.fill(registerVars.length)(LinearCombination(IdealInt.ZERO))
        conj(
          transitionAndVar
            .foldLeft(startVectorSum) {
              case (sums, (t, tVar)) =>
                toMonoid(t)
                  .zip(sums)
                  .map { case (monoidVal, sum) => sum + tVar * monoidVal }
            }
            .zip(registerVars)
            .map { case (rVar, termSum) => rVar === termSum }
        )
      }
    }

    def allNonnegative(vars: Seq[LinearCombination]) = conj(vars.map(_ >= 0))

    Theory.rewritePreds(f, order) { (atom, _) =>
      if (atom.pred == this.predicate) {
        val (transitionVars, registerVars) = atom.splitAt(aut.transitions.size)
        val transitionAndVar = aut.transitions.zip(transitionVars.iterator).to

        val constraints = trace("constraints")(
          List(
            asManyIncomingAsOutgoing(transitionAndVar),
            allNonnegative(transitionVars),
            allNonnegative(registerVars),
            registerValuesReachable(registerVars, transitionAndVar)
          )
        )

        val maybeAtom = if (cycles.isEmpty) List() else List(atom)

        trace(s"Rewriting predicate ${atom} => \n") {
          Conjunction.conj(maybeAtom ++ constraints, order)
        }
      } else atom
    }
  }

  private def termMeansDefinitelyAbsent(
      goal: Goal,
      term: LinearCombination
  ): Boolean = trace(s"termMeansDefinitelyAbsent(${term})") {
    term match {
      case LinearCombination.Constant(x) => x <= 0
      case _                             => goal.reduceWithFacts.upperBound(term).exists(_ <= 0)
    }

  }

  private[this] def transitionStatusFromTerm(
      goal: Goal,
      term: LinearCombination
  ): TransitionSelected = trace(s"selection status for ${term} is ") {
    lazy val lowerBound = goal.reduceWithFacts.lowerBound(term)
    lazy val upperBound = goal.reduceWithFacts.upperBound(term)

    if (lowerBound.exists(_ > 0)) TransitionSelected.Present
    else if (upperBound.exists(_ <= 0)) TransitionSelected.Absent
    else TransitionSelected.Unknown
  }

  def plugin: Option[Plugin] = Some(ConnectednessPropagator)

  /**
   * Generate a quantified formula that is satisfiable iff the provided
   * register values are possible by any legal path through the automaton.
   *
    **/
  def allowsRegisterValues(registerValues: Seq[ITerm]): IFormula = {
    import IExpression._
    val transitionTermSorts = List.fill(autGraph.edges.size)(Sort.Integer) //
    val transitionTerms = autGraph.edges.indices.map(v)

    // need to prevent variable capture by the quantifiers added below
    val shiftedRegisterValues =
      registerValues map (VariableShiftVisitor(_, 0, transitionTermSorts.size))

    ex(
      transitionTermSorts,
      this.predicate(transitionTerms ++ shiftedRegisterValues: _*)
    )
  }

}

object ParikhTheory {
  def apply[A <: Automaton](_aut: A)(
      _toMonoid: _aut.Transition => Seq[LinearCombination]
  ) = new ParikhTheory[A] {
    val aut: _aut.type = _aut
    override def toMonoid(t: _aut.Transition) = _toMonoid(t)

    TheoryRegistry register this
  }
}
