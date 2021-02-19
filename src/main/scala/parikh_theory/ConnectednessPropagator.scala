package uuverifiers.parikh_theory
import ap.proof.theoryPlugins.Plugin
import ap.terfor.preds.Atom
import ap.proof.goal.Goal
import ap.parser.IExpression.Predicate
import ap.terfor.TerForConvenience._

/**
 * A theory plugin that will handle the connectedness of a given automaton,
 * associated with a given predicate, eliminating that predicate upon
 * subsumption.
 */
class ConnectednessPropagator[A <: Automaton](
    private val aut: A,
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
    termMeansDefinitelyAbsent
  }
  lazy private val autGraph = aut.toGraph

  override val procedurePredicate = connectedPredicate
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
          aut.transitions.zip(transitionTerms.iterator).toMap
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
              Seq(predicateAtom),
              unreachableConstraints,
              theoryInstance
            )
          )
      }

      unreachableActions ++ splittingActions
    }
}
