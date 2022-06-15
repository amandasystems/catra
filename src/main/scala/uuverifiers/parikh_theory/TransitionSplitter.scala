package uuverifiers.parikh_theory

import ap.parser.IExpression.Predicate
import ap.proof.theoryPlugins.Plugin
import ap.terfor.preds.Atom
import ap.proof.goal.Goal
import ap.terfor.TerForConvenience._
import ap.terfor.{Term, TermOrder}
import uuverifiers.common._

sealed case class TransitionSplitter(private val theoryInstance: ParikhTheory)
    extends PredicateHandlingProcedure
    with Tracing {

  private val materialisedAutomata =
    theoryInstance.monoidMapPlugin.materialisedAutomata
  private val transitionPredicate = theoryInstance.transitionMaskPredicate
  override val procedurePredicate: Predicate = transitionPredicate

  private def unmaterialisedUnconnectedAutomata(
      context: Context
  ): Iterable[Int] =
    context
      .shuffle(
        context.activeAutomata
          .intersect(context.automataWithConnectedPredicate)
      )

  private def automataToSplit(context: Context): Iterable[Int] =
    unmaterialisedUnconnectedAutomata(context) concat context
      .shuffle(
        context.automataWithConnectedPredicate diff context.activeAutomata
      )

  def splitOnRandomUnknown(
      context: Context,
      auts: Iterable[Int]
  ): Option[Term] = {
    auts
      .map(
        aId =>
          materialisedAutomata(aId).transitions
            .filter(context.transitionStatus(aId)(_).isUnknown)
            .map(context.autTransitionTerm(aId))
      )
      .find(_.nonEmpty)
      .flatMap(someTerms => context.chooseRandomly(someTerms))
  }

  private def trySplittingComponent(
      context: Context,
      auts: Iterable[Int]
  ): Option[Term] =
    auts
      .map(splitToCutComponent(context, _))
      .find(_.isDefined)
      .flatten

  private def splitToCutComponent(
      context: Context,
      automatonId: Int
  ): Option[Term] = trace("splitToCutComponent") {
    val thisAutomaton = materialisedAutomata(automatonId)

    context
      .shuffle(
        thisAutomaton
          .stronglyConnectedComponents()
          .filterNot(scc => scc contains thisAutomaton.initialState)
      )
      .map { scc =>
        thisAutomaton
          .minCut(thisAutomaton.initialState, scc.toSeq.head)
          .map(_._2)
          .filter(context.transitionStatus(automatonId)(_).isUnknown)
          .toSeq // Keep duplicate terms, if any!
          .map(context.autTransitionTerm(automatonId))
      }
      .find(_.nonEmpty)
      .flatMap(someTerms => context.chooseRandomly(someTerms))
  }

  override def handlePredicateInstance(
      goal: Goal
  )(predicateAtom: Atom): Seq[Plugin.Action] = trace("TransitionSplitter") {

    val context = Context(goal, predicateAtom, theoryInstance)
    implicit val order: TermOrder = goal.order

    def transitionToSplit(tTerm: Term) =
      Plugin.AxiomSplit(
        Seq(),
        Seq(tTerm <= 0, tTerm > 0).map(ineq => (conj(ineq), Seq())),
        theoryInstance
      )

    val split = trySplittingComponent(context, automataToSplit(context))
      .orElse(splitOnRandomUnknown(context, automataToSplit(context)))
      .map(t => Seq(transitionToSplit(t)))
      .getOrElse(Seq())

    theoryInstance.runHooks(
      context,
      "Split",
      split
    )
  }
}
