package uuverifiers.parikh_theory

import ap.proof.goal.Goal
import ap.proof.theoryPlugins.Plugin
import ap.terfor.TerForConvenience._
import ap.terfor.preds.Atom
import ap.terfor.conjunctions.{Conjunction, ReduceWithConjunction}
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.{TermOrder, Formula, Term}
import ap.terfor.substitutions.{VariableShiftSubst}
import ap.theories._
import ap.parser.IExpression.Predicate
import ap.terfor.TerForConvenience._

// TODO write a LengthCounting mixin which interns one term for length and
// yields that for each transition
// TODO work through terminology. Why do we use "register values"?
// TODO use [M <: Monoid with Abelian, A <: Automaton]

/**
 * The Parikh Theory enforces Parikh Image membership modulo a morphism to a
 * commutative monoid. The most straightforward example is string length, with
 * an automaton representing the possible strings.
 *
 * NOTE: this is a theory factory, it never registers itself, that's on you, the
 * caller!
 *
 * WARNING! fields are lazy because of how initialisation works in scala (it's
 * Not Great.)
 */
trait ParikhTheory[A <: Automaton]
    extends Theory
    with NoFunctions
    with NoAxioms
    with Tracing
    with Complete {

  val auts: IndexedSeq[A]

  /**
   * This method provides the "modulo" aspect by performing the translation
   * from a transition (usually really the transition's label) to a commutative
   * monoid (M).
   *
   * Must always return something of length monoidDimension.
   *
   * For example length-counting would map all transitions representing a
   * single character (typically all transitions) to 1.
   * NOTE: takes Any argument because Scala's type system isn't sophisticated
   * enough, or I am not sophisticated enough for it. 1-2 of those.
    **/
  def toMonoid(a: (Any, Any, Any)): Seq[LinearCombination]

  /**
   *  This value represents the dimensionality of the sequence returned by
   * `toMonoid`.
    **/
  val monoidDimension: Int

  lazy val aut = auts(0) // lazy because of early init
  lazy private val autGraph = aut.toGraph // lazy because of aut
  // lazy private val cycles = trace("cycles")(autGraph.simpleCycles) // lazy because of aut

  private object TransitionSplitter extends PredicateHandlingProcedure {
    override val procedurePredicate = monoidMapPredicate
    override def handlePredicateInstance(
        goal: Goal
    )(predicateAtom: Atom): Seq[Plugin.Action] = trace("TransitionSplitter") {
      implicit val _ = goal.order

      val transitionTerms =
        trace("transitionTerms")(
          goalTransitionTerms(goal, predicateAtom(0))
        )

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

  /**
   * Take a TransitionMask predicate, and extract its indices.
    **/
  private def transitionMaskToTuple(atom: Atom) = {
    val instanceIdTerm :+ _ :+ tIdxTerm :+ tVal = atom.toSeq
    // TODO in the future, we will need all indices!
    (instanceIdTerm(0), tIdxTerm.constant.intValue, tVal)
  }

  private def goalTransitionTerms(
      goal: Goal,
      instance: LinearCombination
  ) =
    trace(s"TransitionMasks for ${instance} in ${goal}") {
      goal.facts.predConj
        .positiveLitsWithPred(transitionMaskPredicate)
        .map(transitionMaskToTuple)
        .filter { case (i, _, _) => i == instance }
        .sortBy(_._2)
        .map(_._3)
    }

  private object ConnectednessPropagator
      extends Plugin
      with PredicateHandlingProcedure
      with NoAxiomGeneration {
    // Handle a specific predicate instance for a proof goal, returning the
    // resulting plugin actions.
    override val procedurePredicate = monoidMapPredicate
    override def handlePredicateInstance(
        goal: Goal
    )(predicateAtom: Atom): Seq[Plugin.Action] =
      trace("ConnectednessPropagator") {
        implicit val _ = goal.order

        val instanceTerm = predicateAtom(0)

        // TODO in the future we want to filter this for the correct automaton
        val transitionTerms = goalTransitionTerms(goal, instanceTerm)

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
          return trace("Subsumed, schedule actions")(
            Seq(Plugin.RemoveFacts(predicateAtom))
          )
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

        // TODO experiment with branching order and start close to initial
        // states.

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
  // lazy because it depends on aut
  lazy private val monoidMapPredicate =
    new Predicate(s"MonoidMap_${aut.hashCode}", monoidDimension + 1)

  private val transitionMaskPredicate =
    new Predicate(s"TransitionMask_${this.hashCode}", 4)

  override lazy val predicates =
    Seq(monoidMapPredicate, transitionMaskPredicate)

  // TODO do this logic somewhere else!
  // override def preprocess(f: Conjunction, order: TermOrder): Conjunction = {
  //   Theory.rewritePreds(f, order) { (atom, _) =>
  //     if (atom.pred == monoidMapPredicate) {
  //       val maybeAtom = if (cycles.isEmpty) List() else List(atom)

  //       trace(s"Rewriting predicate ${atom} => \n") {
  //         Conjunction.conj(maybeAtom, order)
  //       }
  //     } else atom
  //   }
  // }

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
   * monoid values are possible by any legal path through the automaton.
   */
  def allowsMonoidValues(
      monoidValues: Seq[Term]
  )(implicit order: TermOrder): Formula = {
    assert(monoidValues.length == this.monoidDimension)

    val transitionTerms = autGraph.edges.indices.map(v).toIndexedSeq
    val instanceTerm = l(v(transitionTerms.size))
    val nrNewTerms = transitionTerms.size + 1

    // need to prevent variable capture by the quantifiers added below
    val shiftAwayFromQuantifiers =
      VariableShiftSubst.upShifter[Term](nrNewTerms, order)
    val shiftedMonoidValues = (monoidValues map shiftAwayFromQuantifiers) map (l _)

    val transitionMaskInstances =
      transitionTerms.zipWithIndex
        .map {
          case (t, i) =>
            transitionMaskPredicate(Seq(instanceTerm, l(0), l(i), l(t)))
        }

    val allEquations = exists(
      nrNewTerms,
      conj(
        monoidMapPredicate(instanceTerm +: shiftedMonoidValues) +:
          AutomataFlow(aut).flowEquations(
            transitionTerms.map(l _).toSeq,
            monoidValues.map(l _).toSeq,
            toMonoid _
          ) +:
          transitionMaskInstances
      )
    )

    val simplifiedEquations =
      ReduceWithConjunction(Conjunction.TRUE, order)(allEquations)

    // TODO check if the flow equations have just one solution, in that case just return that.
    // Use  simplifiedEquations.quans: check if empty, and WHAT MORE???
    // TODO also add analysis for simple automata, or perhaps do that earlier?
    trace("allowsMonoidValues")(simplifiedEquations)
  }

}

// TODO turn this into a theory builder?
object ParikhTheory {
  def apply[A <: Automaton](_auts: IndexedSeq[A])(
      _toMonoid: Any => Seq[LinearCombination],
      _monoidDimension: Int
  ) = {
    new ParikhTheory[A] {
      override val auts: IndexedSeq[A] = _auts
      override def toMonoid(t: (Any, Any, Any)) = _toMonoid(t)
      override val monoidDimension = _monoidDimension

      TheoryRegistry register this
    }
  }
}
