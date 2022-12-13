package uuverifiers.parikh_theory

import ap.parser.IExpression.Predicate
import ap.proof.goal.Goal
import ap.proof.theoryPlugins.{Plugin, TheoryProcedure}
import ap.terfor.TerForConvenience._
import ap.terfor.TermOrder
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.preds.Atom
import uuverifiers.common._
import uuverifiers.parikh_theory.VariousHelpers.unlessDo

object TransitionSplitter {
  val BASE_COST = 100
  val SIZE_COST_FACTOR = 10

  private def splitterAddedForThisInstance(context: Context): Atom =
    Atom(
      context.theoryInstance.addedSplitter,
      List(context.instanceTerm),
      context.order
    )

  private def scheduleSplitterForAutomaton(
      context: Context
  )(connectedPred: Atom): Plugin.ScheduleTask = {
    val autNr = context.autNr(connectedPred)
    Plugin.ScheduleTask(
      TransitionSplitter(context.theoryInstance, context.instanceTerm, autNr),
      BASE_COST + context.nrUnknownTransitions(autNr) * SIZE_COST_FACTOR
    )
  }

  def spawnSplitters(context: Context): Seq[Plugin.Action] =
    unlessDo(context.addedSplitterInstances.isEmpty) {
      implicit val order: TermOrder = context.goal.order

      val scheduleSplittersForConnectedPredicates =
        context.connectedInstances.map(scheduleSplitterForAutomaton(context))

      val rememberThatSplitterWasAScheduled =
        Plugin.AddAxiom(
          List(), // Don't we need to know if connected predicates have been removed and add those as reasons?
          conj(splitterAddedForThisInstance(context)),
          context.theoryInstance
        )

      scheduleSplittersForConnectedPredicates appended rememberThatSplitterWasAScheduled
    }

  def spawnSplitter(
      theoryInstance: ParikhTheory,
      predicateInstanceTerm: LinearCombination,
      automataTerm: LinearCombination
  ): Seq[Plugin.Action] =
    // TOOD: take size of automata into account also in this case
    List(
      Plugin.ScheduleTask(
        TransitionSplitter(theoryInstance, predicateInstanceTerm, automataTerm),
        BASE_COST
      )
    )
}

sealed case class TransitionSplitter(
    private val theoryInstance: ParikhTheory,
    predicateInstanceTerm: LinearCombination,
    automataTerm: LinearCombination
) extends PredicateHandlingProcedure
    with Tracing {

  // Note: not the splitter predicate, which is pure book-keeping!
  override val procedurePredicate: Predicate = theoryInstance.monoidMapPredicate
  private val materialisedAutomata =
    theoryInstance.monoidMapPlugin.materialisedAutomata

  def splitOnRandomUnknown(
      context: Context,
      auts: Iterable[Int]
  ): Option[Plugin.Action] = {
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
      .map(tTerm => context.binarySplit(tTerm <= 0))
  }

  private def trySplittingComponent(
      context: Context,
      auts: Iterable[Int]
  ): Option[Plugin.Action] =
    auts
      .map(splitToCutComponent(context, _))
      .find(_.isDefined)
      .flatten

  private def splitToCutComponent(
      context: Context,
      automatonId: Int
  ): Option[Plugin.Action] = trace("splitToCutComponent") {
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
      else transitionsToSever
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

  private val autNr = automataTerm.constant.intValueSafe

  override def handlePredicateInstance(goal: Goal)(
      predicateAtom: Atom
  ): Seq[Plugin.Action] = theoryInstance.withContext(goal, predicateAtom) {
    context =>
      context.connectedInstances.find(context.autNr(_) == autNr) match {
        case Some(a) => {
          import TransitionSplitter.{BASE_COST, SIZE_COST_FACTOR}
          val context = Context(goal, a, theoryInstance)

          val split =
            trySplittingComponent(context, List(autNr))
              .orElse(splitOnRandomUnknown(context, List(autNr)))
              .map(Seq(_))
              .getOrElse(Seq())

          val nrUnknown =
            materialisedAutomata(autNr)
              .transitionsBreadthFirst()
              .count(context.transitionStatus(autNr)(_).isUnknown)

          theoryInstance.runHooks(
            context,
            "Split",
            List(
              Plugin
                .ScheduleTask(this, BASE_COST + nrUnknown * SIZE_COST_FACTOR)
            ) ++ split
          )
        }
        case None =>
          // no more splitting necessary
          List()
      }
  }

  /*
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

 */
}
