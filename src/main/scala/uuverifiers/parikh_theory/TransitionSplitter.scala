package uuverifiers.parikh_theory

import ap.proof.goal.Goal
import ap.proof.theoryPlugins.{Plugin, TheoryProcedure}
import ap.terfor.TerForConvenience.{conj, _}
import ap.terfor.TermOrder
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.preds.Atom
import uuverifiers.common._

trait TransitionSplitter extends TheoryProcedure {
  val theoryInstance: ParikhTheory
  val imageTerm: LinearCombination
  val autId: Int
  val BASE_COST: Int = 100

  private def alreadySpawned(goal: Goal): Boolean =
    goal.facts.predConj
      .positiveLitsWithPred(theoryInstance.addedSplitter)
      .exists(
        parameters =>
          parameters(0) == imageTerm && parameters(1).constant.intValueSafe == autId
      )

  private def markSpawned(goal: Goal) = Plugin.AddAxiom(
    List(),
    conj(
      Atom(
        theoryInstance.addedSplitter,
        List(imageTerm, l(autId)),
        goal.order
      )
    )(
      goal.order
    ),
    theoryInstance
  )
  def spawn(goal: Goal): Seq[Plugin.Action] =
    if (alreadySpawned(goal)) Seq()
    else markSpawned(goal) +: schedule()
  def schedule(): Seq[Plugin.Action] =
    Seq(Plugin.ScheduleTask(this, BASE_COST))

  def chainBefore(lessGoodSplitter: TransitionSplitter): TransitionSplitter = {
    val current = this
    new TransitionSplitter {
      override val theoryInstance: ParikhTheory = current.theoryInstance
      override val imageTerm: LinearCombination = current.imageTerm
      override val autId = current.autId

      override def fallbackSplitter: Option[TransitionSplitter] =
        Some(lessGoodSplitter)

      override def trySplitting(goal: Context): Option[Plugin.Action] =
        current.trySplitting(goal)
    }
  }

  def chainInParallel(otherSplitter: TransitionSplitter): TransitionSplitter = {
    val current = this
    new TransitionSplitter {
      override val theoryInstance: ParikhTheory = current.theoryInstance
      override val imageTerm: LinearCombination = current.imageTerm
      override val autId: Int = current.autId

      override def trySplitting(context: Context): Option[Plugin.Action] = None

      override def schedule(): Seq[Plugin.Action] =
        this.schedule() ++ otherSplitter.schedule()
    }
  }

  def fallbackSplitter: Option[TransitionSplitter] = None
  def trySplitting(context: Context): Option[Plugin.Action]
  private def getContext(goal: Goal) =
    goal.facts.predConj
      .positiveLitsWithPred(theoryInstance.monoidMapPredicate)
      .find(a => a(0) == imageTerm)
      .map(Context(goal, _, theoryInstance))
  override def handleGoal(goal: Goal): Seq[Plugin.Action] =
    getContext(goal)
      .map { context =>
        val thisSplit =
          trySplitting(context)
            .map(_ +: schedule()) // Reschedule if we can do anything!
            .getOrElse(Seq())

        thisSplit elseDo fallbackSplitter
          .map(_.schedule())
          .getOrElse(Seq()) // No splitting was possible: we must be done.
      }
      .getOrElse(Seq()) // MonoidMap not active anymore: stop this splitter
}

sealed class SplitOnRandomUnknown(
    override val theoryInstance: ParikhTheory,
    override val imageTerm: LinearCombination,
    override val autId: Int
) extends TransitionSplitter {

  private def splitOnRandomUnknown(
      context: Context
  ): Option[Plugin.Action] = {
    implicit val order: TermOrder = context.goal.order

    if (!(context.activeAutomata contains autId)) {
      return None
    } // Automaton is no longer active: no splitting needed!

    val thisAutomaton = theoryInstance.automaton(autId)
    val unknownTransitionTerms =
      thisAutomaton
        .transitionsBreadthFirst()
        .filter(
          context
            .transitionStatus(autId)(_)
            .isUnknown
        )
        .map(context.autTransitionTerm(autId))
        .toSeq

    context
      .chooseRandomly(unknownTransitionTerms)
      .map(
        tTerm =>
          theoryInstance
            .logDecision("SplitRandom", context.binarySplit(tTerm <= 0))
      ) // If this is empty, then no unknown terms remain!
  }
  override def trySplitting(context: Context): Option[Plugin.Action] =
    splitOnRandomUnknown(context)
}

sealed class SplitToCutComponent(
    override val theoryInstance: ParikhTheory,
    override val imageTerm: LinearCombination,
    override val autId: Int
) extends TransitionSplitter
    with Tracing {

  override val BASE_COST: Int = 10

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
      .map(
        cut =>
          theoryInstance.logDecision(
            "SplitSever",
            context.binarySplit(eqZ(cut)(context.goal.order))
          )
      )
  }

  override def trySplitting(context: Context): Option[Plugin.Action] =
    if (context.isConnected(autId)) None
    else
      splitToCutComponent(context, autId)

}
