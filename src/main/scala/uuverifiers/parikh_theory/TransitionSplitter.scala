package uuverifiers.parikh_theory

import ap.parser.IExpression.Predicate
import ap.proof.goal.Goal
import ap.proof.theoryPlugins.Plugin
import ap.terfor.TerForConvenience._
import ap.terfor.TermOrder
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.preds.Atom
import uuverifiers.common._

sealed case class TransitionSplitter(private val theoryInstance: ParikhTheory)
    extends PredicateHandlingProcedure
    with Tracing {

  private val materialisedAutomata =
    theoryInstance.monoidMapPlugin.materialisedAutomata
  private val transitionPredicate = theoryInstance.transitionMaskPredicate
  override val procedurePredicate: Predicate = transitionPredicate

  private def automataToSplit(context: Context): Iterable[Int] =
    context
      .shuffle(
        context.automataWithConnectedPredicate union context.activeAutomata
      )
      .toSeq // Ordering is: false before true. SortBy is stable, so shuffling is preserved.
      .sortBy(aId => !(context.activeAutomata contains aId))

  def splitOnRandomUnknown(
      context: Context,
      auts: Iterable[Int]
  ): Option[Plugin.AxiomSplit] = {
    implicit val order: TermOrder = context.goal.order
    auts
      .map(
        aId =>
          materialisedAutomata(aId)
            .transitionsBreadthFirst()
            .filter(context.transitionStatus(aId)(_).isUnknown)
            .map(context.autTransitionTerm(aId))
            .toSeq
      )
      .find(_.nonEmpty)
      .flatMap(someTerms => context.chooseRandomly(someTerms))
      .map(tTerm => context.binarySplit(tTerm === 0))
  }

  private def trySplittingComponent(
      context: Context,
      auts: Iterable[Int]
  ): Option[Plugin.AxiomSplit] =
    auts
      .map(splitToCutComponent(context, _))
      .find(_.isDefined)
      .flatten

  private def splitToCutComponent(
      context: Context,
      automatonId: Int
  ): Option[Plugin.AxiomSplit] = trace("splitToCutComponent") {
    val thisAutomaton = context.filteredAutomaton(automatonId)

    def separatingCut(
        scc: Set[State]
    ): Iterable[LinearCombination] = {
      val transitionsToSever = scc
        .find(thisAutomaton.initialState != _)
        .map(
          sccRepresentative =>
            thisAutomaton
              .minCut(
                thisAutomaton.initialState,
                sccRepresentative
              )
        )
        .getOrElse(Set.empty) // The SCC is just the initial state
        .map(_._2)
        .map(context.autTransitionTerm(automatonId))

      if (transitionsToSever.isEmpty || context
            .knownPositive(transitionsToSever)) Nil
      else transitionsToSever.map(l(_)(context.goal.order))
    }

    context
      .shuffle(
        thisAutomaton
          .stronglyConnectedComponents()
      )
      .map(separatingCut)
      .find(cut => cut.nonEmpty)
      .map(cut => context.binarySplit(eqZ(cut)(context.goal.order)))
  }

  override def handlePredicateInstance(
      goal: Goal
  )(predicateAtom: Atom): Seq[Plugin.Action] = trace("TransitionSplitter") {

    val context = Context(goal, predicateAtom, theoryInstance)

    val split =
      trySplittingComponent(context, automataToSplit(context))
        .orElse(splitOnRandomUnknown(context, automataToSplit(context)))
        .map(Seq(_))
        .getOrElse(Seq())

    theoryInstance.runHooks(
      context,
      "Split",
      split
    )
  }
}
