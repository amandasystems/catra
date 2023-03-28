package uuverifiers.parikh_theory

import ap.proof.goal.Goal
import ap.proof.theoryPlugins.{Plugin, TheoryProcedure}
import ap.terfor.TerForConvenience._
import ap.terfor.TermOrder
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.preds.Atom
import uuverifiers.common._

object TransitionSplitter {
  val BASE_COST = 100
  val SIZE_COST_FACTOR = 10

  def spawnSplitters(
      goal: Goal,
      theoryInstance: ParikhTheory
  ): Seq[Plugin.Action] =
    if (goal.facts.predicates contains theoryInstance.addedSplitter) {
      List()
    } else {
      implicit val order = goal.order

      val connectedLits =
        goal.facts.predConj
          .positiveLitsWithPred(theoryInstance.connectedPredicate)
      val transitionLits =
        goal.facts.predConj
          .positiveLitsWithPred(theoryInstance.transitionMaskPredicate)

      val tasks =
        for (a <- connectedLits) yield {
          val transitions =
            for (b <- transitionLits; if a(0) == b(0) && a(1) == b(1)) yield b
          Plugin.ScheduleTask(
            TransitionSplitter(theoryInstance, a(0), a(1)),
            BASE_COST + transitions.size * SIZE_COST_FACTOR
          )
        }

      // we add a flag to remember that the tasks for splitting have
      // already been created
      val splitterAct =
        Plugin.AddAxiom(
          List(),
          conj(Atom(theoryInstance.addedSplitter, List(), order)),
          theoryInstance
        )

      tasks ++ List(splitterAct)
    }

  def spawnSplitter(
      theoryInstance: ParikhTheory,
      imageTerm: LinearCombination,
      automataTerm: LinearCombination
  ): Seq[Plugin.Action] =
    // TOOD: take size of automata into account also in this case
    List(
      Plugin.ScheduleTask(
        TransitionSplitter(theoryInstance, imageTerm, automataTerm),
        BASE_COST
      )
    )
}

sealed case class TransitionSplitter(
    private val theoryInstance: ParikhTheory,
    imageTerm: LinearCombination,
    automataTerm: LinearCombination
) extends TheoryProcedure
    with Tracing {

  private val materialisedAutomata =
    theoryInstance.monoidMapPlugin.materialisedAutomata
//  private val transitionPredicate = theoryInstance.transitionMaskPredicate
//  override val procedurePredicate: Predicate = transitionPredicate

  /*
  private def automataToSplit(context: Context): Iterable[Int] =
    context
      .shuffle(
        context.automataWithConnectedPredicate union context.activeAutomata
      )
      .toSeq // Ordering is: false before true. SortBy is stable, so shuffling is preserved.
      .sortBy(aId => !(context.activeAutomata contains aId))
   */

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

  val autNr = automataTerm.constant.intValueSafe

  override def handleGoal(goal: Goal): Seq[Plugin.Action] = {
    val connectedLits =
      goal.facts.predConj
        .positiveLitsWithPred(theoryInstance.connectedPredicate)
    connectedLits.find(a => a(0) == imageTerm && a(1) == automataTerm) match {
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

        theoryInstance.logDecision(
          "Split",
          List(
            Plugin.ScheduleTask(this, BASE_COST + nrUnknown * SIZE_COST_FACTOR)
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
