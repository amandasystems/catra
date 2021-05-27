package uuverifiers.parikh_theory
import ap.proof.theoryPlugins.Plugin
import ap.terfor.preds.Atom
import ap.proof.goal.Goal
import ap.parser.IExpression.Predicate
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.TerForConvenience._
import ap.terfor.Formula

/**
 * A theory plugin that will handle the connectedness of a given automaton,
 * associated with a given predicate, eliminating that predicate upon
 * subsumption.
 */
class ConnectednessPropagator[A <: Automaton](
    private val auts: IndexedSeq[A],
    private val connectedPredicate: Predicate,
    private val transitionPredicate: Predicate,
    private val transitionExtractor: TransitionMaskExtractor,
    private val theoryInstance: ParikhTheory[A]
) extends Plugin
    with PredicateHandlingProcedure
    with NoAxiomGeneration
    with Tracing {

  import transitionExtractor.{
    goalTransitionTerms,
    transitionStatusFromTerm,
    termMeansDefinitelyAbsent,
    goalAssociatedPredicateInstances
  }

  override val procedurePredicate = connectedPredicate
  override def handlePredicateInstance(
      goal: Goal
  )(predicateAtom: Atom): Seq[Plugin.Action] =
    trace("ConnectednessPropagator") {
      val instanceTerm = predicateAtom(0)

      // TODO in the future we want to filter this for the correct automaton
      val (transitionTerms, currentProductDepth) =
        goalTransitionTerms(goal, instanceTerm)

      // NOTE it might be a good idea to start removing transitions from past
      // levels of products for efficiency. In that case, this check will only
      // work if we are really, really sure to not keep any old TransitionMask
      // predicates around, or they might show up, be unspecified, and thus
      // cause us to never terminate.
      // FIXME this is highly inefficient repeat work and should be factored
      // out.
      val isSubsumed = trace("isSubsumed") {
        transitionTerms.isEmpty || (!(transitionTerms exists (
            t => transitionStatusFromTerm(goal, t).isUnknown
        )) && currentProductDepth == (auts.size + 1))
      }

      val transitionMasks = goalAssociatedPredicateInstances(
        goal,
        instanceTerm,
        transitionPredicate
      )

      if (isSubsumed) {
        val associatedPredicates = transitionMasks ++ goalAssociatedPredicateInstances(
          goal,
          instanceTerm,
          theoryInstance.predicates(0)
        )

        // FIXME the extraction of the predicates is REALLY ugly!

        return trace("Subsumed, schedule actions")(
          associatedPredicates.map(Plugin.RemoveFacts(_)) :+ Plugin.RemoveFacts(
            predicateAtom
          )
        )
      } else {
        return propagateOrSplitConnectedness(
          goal,
          transitionTerms,
          currentProductDepth,
          predicateAtom
        )
      }
    }

  private def propagateOrSplitConnectedness(
      goal: Goal,
      transitionTerms: Seq[LinearCombination],
      currentProductDepth: Int,
      predicateAtom: Atom
  ) = trace("propagateOrSplitConnectedness") {

    val instanceTerm = predicateAtom(0)
    val transitionMasks: Seq[Formula] = goalAssociatedPredicateInstances(
      goal,
      instanceTerm,
      transitionPredicate
    )

    // first compute current product
    // after that, check if *that* is connected
    // after that, check if we should materialise the next level or stay here

    // if we are staying, maintain the branching logic

    implicit val order = goal.order
    val aut = auts(0)
    val autGraph = aut.toGraph

    val transitionToTerm =
      trace("transitionToTerm")(
        aut.transitions.zip(transitionTerms.iterator).toMap
      )

    val splittingActions = trace("splittingActions") {
      val splitter = new TransitionSplitter(
        transitionPredicate,
        transitionExtractor,
        theoryInstance
      )
      goalState(goal) match {
        case Plugin.GoalState.Final => splitter.handleGoal(goal)
        case _                      => List(Plugin.ScheduleTask(splitter, 0))
      }
    }

    // TODO: we don't care about splitting edges that cannot possibly cause a
    // disconnect; i.e. *we only care* about critical edges on the path to
    // some cycle that can still appear (i.e. wose edges are not
    // known-deselected).

    // TODO experiment with branching order and start close to initial
    // states.

    // TODO compute a cut to find which dead transitions contribute to the conflict!

    // constrain any terms associated with a transition from a
    // *known* unreachable state to be = 0 ("not used").
    val unreachableActions = trace("unreachableActions") {
      val deadTransitions = trace("deadTransitions") {
        aut.transitions
          .filter(
            t => termMeansDefinitelyAbsent(goal, transitionToTerm(t))
          )
          .toSet
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
            transitionMasks :+ predicateAtom, // FIXME add deadTransitions transitionMask:s
            unreachableConstraints,
            theoryInstance
          )
        )
    }

    unreachableActions ++ splittingActions
  }
}
