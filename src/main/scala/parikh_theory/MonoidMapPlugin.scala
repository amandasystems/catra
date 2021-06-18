package uuverifiers.parikh_theory
import ap.proof.theoryPlugins.Plugin
import ap.terfor.preds.Atom
import ap.terfor.Term
import ap.proof.goal.Goal
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.TerForConvenience._
import scala.collection.mutable.ArrayBuffer
import scala.collection.SortedSet
import ap.terfor.conjunctions.Conjunction
import collection.mutable.HashMap

/**
 * A theory plugin that will handle the connectedness of a given automaton,
 * associated with a given predicate, eliminating that predicate upon
 * subsumption.
 */
class MonoidMapPlugin[A <: Automaton](
    private val theoryInstance: ParikhTheory[A]
) extends Plugin
    with PredicateHandlingProcedure
    with NoAxiomGeneration
    with Tracing {

  private val transitionExtractor = new TransitionMaskExtractor(
    theoryInstance.transitionMaskPredicate
  )

  import transitionExtractor.{
    transitionStatusFromTerm,
    termMeansDefinitelyAbsent,
    goalAssociatedPredicateInstances,
    automataNr,
    transitionNr,
    transitionTerm,
    connectedAutId
  }

  // A cache for materialised automata. The first ones are the same as auts.
  private val materialisedAutomata = ArrayBuffer[A](theoryInstance.auts: _*)

  override val procedurePredicate = theoryInstance.monoidMapPredicate

  private val stats = new Statistics()

  /**
   *  This callback is the entrypoint of the connectedness enforcement. It will
   *  determine subsumption, i.e. if there are no unknown transitions left on
   *  the last level of the prdouct. Upon subsumption it will remove the
   *  connectedness predicate and all associated helper predicates.
   *
   *  If we are not subsumed, we will continue with propagation or splitting.
   */
  override def handlePredicateInstance(
      goal: Goal
  )(predicateAtom: Atom): Seq[Plugin.Action] =
    trace("MonoidMapPlugin") {
      val context = Context(goal, predicateAtom)
      stats.increment("handlePredicateInstance")

      // FIXME!!!
      val materialiseActions =
        if (context.activeAutomata.size > 1)
          handleMaterialise(context)
        else Seq()

      handleMonoidMapSubsumption(context) ++ context.connectedInstances.flatMap(
        handleConnectedInstance(_, context)
      ) ++ materialiseActions ++ handleSplitting(context)
    }

  private def handleMonoidMapSubsumption(context: Context) =
    trace("handleMonoidMapSubsumption") {
      import context.{
        activeAutomata,
        connectedInstances,
        monoidMapPredicateAtom,
        transitionMasks
      }

      val productIsDone =
        trace("productIsDone")(activeAutomata.size <= 1)
      val allAutomataGuaranteedConnected = connectedInstances.isEmpty
      val isSubsumed =
        trace("isSubsumed")(productIsDone && allAutomataGuaranteedConnected)

      if (isSubsumed) {
        val removeAssociatedPredicates =
          transitionMasks.map(Plugin.RemoveFacts(_))
        val removeThisPredicateInstance =
          Plugin.RemoveFacts(monoidMapPredicateAtom)

        stats.report()

        removeAssociatedPredicates :+ removeThisPredicateInstance
      } else {
        Seq()
      }
    }

  // TODO use Context here to inject more information!
  private def handleSplitting(context: Context) = trace("handleSplitting") {
    stats.increment("handleSplitting")
    val splitter = new TransitionSplitter()

    goalState(context.goal) match {
      case Plugin.GoalState.Final => splitter.handleGoal(context.goal)
      case _                      => List(Plugin.ScheduleTask(splitter, 0))
    }
  }

  private def handleMaterialise(context: Context) = trace("handleMaterialise") {
    val knownConnectedAutomataNrs: Seq[Int] =
      trace("knownConnectedAutomataNrs")(
        context.activeAutomata
          .diff(context.automataWithConnectedPredicate)
          .toSeq
      )

    // TODO better heuristic for >2!
    // TODO should we start materialise single automata?
    knownConnectedAutomataNrs match {
      case Seq()  => Seq()
      case Seq(_) => Seq()
      case Seq(left, right) =>
        materialiseProduct(left, right, context)
      case fst +: snd +: _ =>
        materialiseProduct(fst, snd, context)
    }
  }

  // TODO make this a PredicateHandlingProcedure?
  private def handleConnectedInstance(
      connectedInstance: Atom,
      context: Context
  ) = trace(s"handleConnectedInstance ${connectedInstance}") {

    val autId = connectedAutId(connectedInstance)
    val myTransitionMasks = context.autTransitionMasks(autId)
    val aut = materialisedAutomata(autId)
    val transitionToTerm = context.autTransitionTerm(autId)(_)

    implicit val order = context.goal.order
    val autGraph = aut.toGraph

    // TODO: we don't care about splitting edges that cannot possibly cause a
    // disconnect; i.e. *we only care* about critical edges on the path to
    // some cycle that can still appear (i.e. wose edges are not
    // known-deselected).
    // this relates to a MST

    // TODO experiment with branching order and start close to initial
    // states.

    // TODO compute a cut to find which dead transitions contribute to the conflict!

    val deadTransitions = trace("deadTransitions") {
      aut.transitions
        .filter(
          t => termMeansDefinitelyAbsent(context.goal, transitionToTerm(t))
        )
        .toSet
    }

    val knownUnreachableEdges = trace("knownUnreachableEdges") {
      autGraph
        .dropEdges(deadTransitions)
        .unreachableFrom(aut.initialState)
    }

    // val possiblyUnreachableEdges = trace("possiblyUnreachableEdges") {
    //   autGraph
    //     .dropEdges(maybeDeadTransitions)
    //     .unreachableWithFilterFrom(aut.initialState, t => termMeansPossiblyAbsent(goal, transitionToTerm(t)))
    // }
    // FIXME why doesn't this work for subsumption? possiblyUnreachableEdges.isEmpty
    // FIXME because we also drop the CYCLE edges that may be unreachable!!!
    // FIXME this requires a custom automata thing where we don't walk an unsure edge, but we don't remove them fully

    val unknownEdges = trace("unknownEdges")(
      context.autTransitionTermsUnordered(autId) filter (
          t => transitionStatusFromTerm(context.goal, t).isUnknown
      )
    )

    val allTransitionsAssigned = unknownEdges.isEmpty || context
      .autTransitionTermsUnordered(autId)
      .isEmpty

    val subsumeActions =
      if (allTransitionsAssigned) Seq(Plugin.RemoveFacts(connectedInstance))
      else Seq()

    // constrain any terms associated with a transition from a
    // *known* unreachable state to be = 0 ("not used").
    val unreachableActions = trace("unreachableActions") {
      val unreachableConstraints =
        conj(
          knownUnreachableEdges
            .flatMap(
              autGraph.transitionsFrom(_).map(transitionToTerm(_) === 0)
            )
        )

      if (unreachableConstraints.isTrue) Seq()
      else
        Seq(
          Plugin.AddAxiom(
            myTransitionMasks :+ connectedInstance, // FIXME limit to deadTransitions transitionMask:s
            unreachableConstraints,
            theoryInstance
          )
        )
    }

    unreachableActions ++ subsumeActions

  }

  private def materialiseProduct(
      leftId: Int,
      rightId: Int,
      context: Context
  ) = {
    stats.increment("materialiseProduct")

    val left = context.filteredAutomaton(leftId)
    val right = context.filteredAutomaton(rightId)
    trace(
      s"materialising product of ${left.transitions.toSeq} and ${right.transitions.toSeq}"
    )("")

    val (product, termToProductEdges) = left.productWithSources(right)

    val newAutomataNr = trace("newAutomataNr")(materialisedAutomata.size)
    materialisedAutomata += product.asInstanceOf[A]

    val removeTransitionMasks =
      context.transitionMasks.map(Plugin.RemoveFacts(_))
    val removeConnectedPredicates = context.connectedInstances
      .filter(m => automataNr(m) == leftId || automataNr(m) == rightId)
      .map(Plugin.RemoveFacts(_))

    // TODO figure out how to generate a nice blocking clause
    val productClauses = if (product.isEmpty()) {
      Seq(
        Plugin.AddAxiom(
          context.autTransitionMasks(leftId) ++ context.autTransitionMasks(
            rightId
          ) :+ context.monoidMapPredicateAtom,
          Conjunction.FALSE,
          theoryInstance
        )
      )
    } else {
      formulaForNewAutomaton(
        newAutomataNr,
        leftId,
        rightId,
        termToProductEdges
          .asInstanceOf[Map[(Any, Any, Any), Seq[(Any, Any, Any)]]],
        context
      )

    }

    removeTransitionMasks ++ removeConnectedPredicates ++ productClauses
  }

  private def formulaForNewAutomaton(
      productNr: Int,
      leftNr: Int,
      rightNr: Int,
      termToProductEdges: Map[(Any, Any, Any), Seq[(Any, Any, Any)]],
      context: Context
  ) = {
    import ap.basetypes.IdealInt.ZERO
    import scala.language.existentials

    implicit val order = context.goal.order
    val varFactory = new FreshVariables(0)
    val transitionToTerm = trace("product transitionToTerm")(
      materialisedAutomata(productNr).transitions
        .map(t => (t, varFactory.nextVariable()))
        .toMap
    )

    val newClauses = theoryInstance.automataClauses(
      materialisedAutomata(productNr),
      context.instanceTerm,
      productNr,
      transitionToTerm.toIndexedSeq
    )

    // - x(t) = sum(e : termProductEdges(t, default=0))
    val bridgingClauses = trace("Bridging clauses") {
      val productTransitionToLc = transitionToTerm
        .asInstanceOf[Map[(Any, Any, Any), Term]]
        .andThen(l(_)(order))

      Seq(leftNr, rightNr).flatMap(
        autNr => {
          val transitionToTerm = context.autTransitionTerm(autNr)(_)

          materialisedAutomata(autNr).transitions.map(
            termTransition =>
              trace(s"a${autNr} bridge: ${termTransition}")(
                transitionToTerm(termTransition) === termToProductEdges
                  .get(termTransition)
                  .map(
                    productEdges =>
                      lcSum(productEdges.map(productTransitionToLc))
                  )
                  .getOrElse(
                    trace(
                      s"a${autNr}::${termTransition} not in product ${productNr}"
                    )(l(ZERO))
                  )
              )
          )
        }
      )

    }

    // FIXME maybe simplify?

    Seq(
      Plugin.AddAxiom(
        context.autTransitionMasks(leftNr) ++ context.autTransitionMasks(
          rightNr
        ) :+ context.monoidMapPredicateAtom,
        varFactory.exists(conj(newClauses ++ bridgingClauses)),
        theoryInstance
      )
    )

  }

  /**
   * This class captures common contextual values that can be extracted from a
   * proof goal.
   */
  sealed case class Context(val goal: Goal, val monoidMapPredicateAtom: Atom) {
    val instanceTerm = monoidMapPredicateAtom(0)

    private val transitionTermCache = HashMap[Int, Map[(Any, Any, Any), Term]]()

    lazy val connectedInstances = trace("connectedInstances")(
      goalAssociatedPredicateInstances(
        goal,
        instanceTerm,
        theoryInstance.connectedPredicate
      )
    )

    lazy val automataWithConnectedPredicate = SortedSet(
      connectedInstances.map(connectedAutId): _*
    )

    lazy val transitionMasks = trace("transitionMasks")(
      goalAssociatedPredicateInstances(
        goal,
        instanceTerm,
        theoryInstance.transitionMaskPredicate
      )
    )

    lazy val activeAutomata = trace("activeAutomata") {
      SortedSet(
        transitionMasks
          .map(automataNr): _*
      )
    }

    private def getOrUpdateTransitionTermMap(autId: Int) = {
      val autMap: Map[(Any, Any, Any), Term] =
        transitionTermCache.getOrElseUpdate(
          autId,
          trace(s"getOrUpdateTransitionTermMap::compute(${autId})")(
            materialisedAutomata(autId).transitions
              .zip(autTransitionMasks(autId).map(transitionTerm).iterator)
              .toMap
          )
        )
      autMap
    }

    def autTransitionTerm(autId: Int)(transition: (Any, Any, Any)): Term =
      getOrUpdateTransitionTermMap(autId)(transition)

    def autTransitionTermsUnordered(autId: Int) =
      getOrUpdateTransitionTermMap(autId).values

    // FIXME memoise
    def autTransitionMasks(autId: Int) =
      transitionMasks
        .filter(automataNr(_) == autId)
        .sortBy(transitionNr)
        .toIndexedSeq

    // FIXME excellent candidate for memoisation!
    def filteredAutomaton(autId: Int) =
      materialisedAutomata(autId).filterTransitions(
        t =>
          !termMeansDefinitelyAbsent(
            goal,
            l(autTransitionTerm(autId)(t))(goal.order)
          )
      )

    val monoidValues = monoidMapPredicateAtom.tail
  }

  class TransitionSplitter() extends PredicateHandlingProcedure with Tracing {

    import transitionExtractor.transitionStatusFromTerm

    private val transitionPredicate = theoryInstance.transitionMaskPredicate
    override val procedurePredicate = transitionPredicate

    override def handlePredicateInstance(
        goal: Goal
    )(predicateAtom: Atom): Seq[Plugin.Action] = trace("TransitionSplitter") {

      val context = Context(goal, predicateAtom)
      implicit val order = goal.order

      val unknownTransitions = trace("unknownTransitions") {
        context.automataWithConnectedPredicate.unsorted
          .flatMap(context.autTransitionTermsUnordered)
          .filter(
            t => transitionStatusFromTerm(goal, t).isUnknown
          )
      }

      trace("unknownActions") {
        def transitionToSplit(transitionTerm: LinearCombination) =
          Plugin.AxiomSplit(
            Seq(),
            Seq(transitionTerm <= 0, transitionTerm > 0)
              .map(eq => (conj(eq), Seq())),
            theoryInstance
          )

        val splittingActions = trace("splittingActions") {
          unknownTransitions
            .map(transitionToSplit(_))
            .toSeq
        }

        if (splittingActions.isEmpty) Seq() else Seq(splittingActions.head)

      }
    }
  }

}
