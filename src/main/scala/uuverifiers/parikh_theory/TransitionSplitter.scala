package uuverifiers.parikh_theory

import ap.proof.theoryPlugins.Plugin
import ap.terfor.preds.Atom
import ap.proof.goal.Goal
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.TerForConvenience._
import uuverifiers.common._

sealed case class TransitionSplitter(private val theoryInstance: ParikhTheory)
    extends PredicateHandlingProcedure
    with Tracing {

  private val materialisedAutomata =
    theoryInstance.monoidMapPlugin.materialisedAutomata
  private val transitionPredicate = theoryInstance.transitionMaskPredicate
  override val procedurePredicate = transitionPredicate

  override def handlePredicateInstance(
      goal: Goal
  )(predicateAtom: Atom): Seq[Plugin.Action] = trace("TransitionSplitter") {

    val context = Context(goal, predicateAtom, theoryInstance)
    implicit val order = goal.order

    val unknownTransitions = trace("unknownTransitions") {
      context.automataWithConnectedPredicate.toSeq
        .flatMap { aNr =>
          materialisedAutomata(aNr)
            .transitionsBreadthFirst()
            .filter(
              context.transitionStatus(aNr)(_).isUnknown
            )
            .map(context.autTransitionTerm(aNr))
        }
    }

    // TODO: need a proper cut here
    def transitionToSplit(tTerm: LinearCombination) =
      Plugin.AxiomSplit(
        Seq(conj(tTerm >= 0)),
        Seq(tTerm === 0, tTerm > 0).map(ineq => (conj(ineq), Seq())),
        theoryInstance
      )

    val rand = ap.parameters.Param.RANDOM_DATA_SOURCE(goal.settings)
    val allSplits = unknownTransitions.map(transitionToSplit(_)).toSeq
    val split =
      if (allSplits.isEmpty)
        List()
      else
        List(allSplits(rand nextInt allSplits.size))

    theoryInstance.runHooks(
      context,
      "Split",
      split
    )
  }
}
