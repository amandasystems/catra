package uuverifiers.parikh_theory

import ap.parser.IExpression.Predicate
import ap.proof.goal.Goal
import ap.proof.theoryPlugins.{Plugin, TheoryProcedure}
import ap.terfor.TerForConvenience._
import ap.terfor.{TermOrder, Term}
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.preds.Atom
import uuverifiers.common._

object TransitionSplitter {
  val BASE_COST = 100

  def spawnSplitters(goal : Goal,
                     theoryInstance: ParikhTheory) : Seq[Plugin.Action] =
    if (goal.facts.predicates contains theoryInstance.addedSplitter) {
      List()
    } else {
      implicit val order = goal.order

      val connectedLits =
        goal.facts.predConj.positiveLitsWithPred(
          theoryInstance.connectedPredicate)
      val tasks =
        for (a <- connectedLits) yield {
          Plugin.ScheduleTask(
            TransitionSplitter(theoryInstance, a(0), a(1)), BASE_COST)
        }
//println(tasks)
      tasks ++ List(
        Plugin.AddAxiom(
          List(),
          conj(Atom(theoryInstance.addedSplitter, List(), order)),
          theoryInstance))
    }

  def spawnSplitter(theoryInstance: ParikhTheory,
                    imageTerm : Term,
                    automataTerm : Term) : Seq[Plugin.Action] = {
    val res = List(
      Plugin.ScheduleTask(
        TransitionSplitter(theoryInstance, imageTerm, automataTerm), BASE_COST))
//    println(res)
    res
  }
}

sealed case class TransitionSplitter(private val theoryInstance: ParikhTheory,
                                     imageTerm : Term,
                                     automataTerm : Term)
    extends TheoryProcedure
    with Tracing {

  private val materialisedAutomata =
    theoryInstance.monoidMapPlugin.materialisedAutomata
  private val transitionPredicate = theoryInstance.transitionMaskPredicate
//  override val procedurePredicate: Predicate = transitionPredicate

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
      .map(tTerm => context.binarySplit(tTerm === 0))
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

  val autNr =
    automataTerm.asInstanceOf[LinearCombination].constant.intValueSafe

  override def handleGoal(goal: Goal): Seq[Plugin.Action] = {
    val connectedLits =
      goal.facts.predConj.positiveLitsWithPred(theoryInstance.connectedPredicate)
    connectedLits.find(
      a => a(0) == imageTerm && a(1) == automataTerm) match {
      case Some(a) => {
//        println("splitting: " + a)

        val context = Context(goal, a, theoryInstance)

/*        val split =
          trySplittingComponent(context, List(autNr))
            .orElse(splitOnRandomUnknown(context, List(autNr)))
            .map(Seq(_))
            .getOrElse(Seq()) */
        val split =
          splitOnRandomUnknown(context, List(autNr))
            .map(Seq(_))
            .getOrElse(Seq())

/*
        val nrUnknown =
          materialisedAutomata(autNr)
            .transitionsBreadthFirst()
            .filter(context.transitionStatus(autNr)(_).isUnknown)
            .size
 */

//println(nrUnknown)
//println(split)

        theoryInstance.runHooks(
          context,
          "Split",
          List(Plugin.ScheduleTask(
                 this, TransitionSplitter.BASE_COST)) ++ split
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
