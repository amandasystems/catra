package uuverifiers.parikh_theory
import ap.terfor.preds.Atom
import ap.proof.goal.Goal
import ap.proof.theoryPlugins.Plugin
import ap.parser.IExpression.Predicate
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.TerForConvenience._

class TransitionSplitter(
    private val transitionPredicate: Predicate,
    private val transitionExtractor: TransitionMaskExtractor,
    private val theoryInstance: ParikhTheory[_]
) extends PredicateHandlingProcedure
    with Tracing {
  import transitionExtractor.{goalTransitionTerms, transitionStatusFromTerm}

  override val procedurePredicate = transitionPredicate
  override def handlePredicateInstance(
      goal: Goal
  )(predicateAtom: Atom): Seq[Plugin.Action] = trace("TransitionSplitter") {
    implicit val order = goal.order

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
