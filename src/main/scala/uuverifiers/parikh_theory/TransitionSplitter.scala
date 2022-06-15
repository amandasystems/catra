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

  private def unmaterialisedUnconnectedAutomata(context: Context) =
    context.activeAutomata
      .intersect(context.automataWithConnectedPredicate)
      .toSeq

  private def selectAutomatonToSplit(context: Context): Option[Int] =
    (context chooseRandomly unmaterialisedUnconnectedAutomata(context)).orElse(
      context chooseRandomly context.automataWithConnectedPredicate.toSeq
    )

  def splitOnRandomUnknown(context: Context, automatonId: Int): Option[Term] =
    context.chooseRandomly(
      materialisedAutomata(automatonId).transitions
        .filter(context.transitionStatus(automatonId)(_).isUnknown)
        .map(context.autTransitionTerm(automatonId))
    )

  private def selectTransitionTermToSplit(
      context: Context,
      automatonId: Int
  ): Option[Term] =
    splitToCutComponent(context, automatonId) orElse
      splitOnRandomUnknown(context, automatonId)

  private def splitToCutComponent(
      context: Context,
      automatonId: Int
  ): Option[Term] = trace("splitToCutComponent") {
    val thisAutomaton = materialisedAutomata(automatonId)

    context.chooseRandomly(
      context
        .chooseRandomly(
          thisAutomaton
            .stronglyConnectedComponents()
            .toSeq // Impossible to cut a component containing the initial state
            .filterNot(scc => scc contains thisAutomaton.initialState)
        )
        .map { randomSCC =>
          thisAutomaton
            .minCut(thisAutomaton.initialState, randomSCC.toSeq.head)
            .map(_._2)
            .filter(context.transitionStatus(automatonId)(_).isUnknown)
            .toSeq // Keep duplicate terms, if any!
            .map(context.autTransitionTerm(automatonId))
        }
        .getOrElse(Seq.empty)
    )
  }

  override def handlePredicateInstance(
      goal: Goal
  )(predicateAtom: Atom): Seq[Plugin.Action] = trace("TransitionSplitter") {

    val context = Context(goal, predicateAtom, theoryInstance)
    implicit val order: TermOrder = goal.order

    def transitionToSplit(tTerm: Term) =
      Plugin.AxiomSplit(
        Seq(conj(tTerm >= 0)),
        Seq(tTerm === 0, tTerm > 0).map(ineq => (conj(ineq), Seq())),
        theoryInstance
      )

    val split = selectAutomatonToSplit(context)
      .flatMap(aId => selectTransitionTermToSplit(context, aId))
      .map(t => Seq(transitionToSplit(t)))
      .getOrElse(Seq())

    theoryInstance.runHooks(
      context,
      "Split",
      split
    )
  }
}
