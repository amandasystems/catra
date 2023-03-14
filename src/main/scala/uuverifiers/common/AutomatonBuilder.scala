package uuverifiers.common

import scala.collection.{SortedSet, mutable}

class AutomatonBuilder extends Tracing {
  private var _autStates = SortedSet[State]()
  private var _outgoingTransitions = Map[State, SortedSet[Transition]]()
  private var _initial: Option[State] = None
  private var _accepting = Set[State]()
  private var name: Option[String] = None
  private val forward = new IncrementallyReachable[State]
  private var backward = new IncrementallyReachable[State]

  def nameIs(n: String): AutomatonBuilder = {
    this.name = Some(n)
    this
  }

  def containsState(s: State): Boolean = _autStates contains s

  def containsTransition(t: Transition): Boolean = {
    _outgoingTransitions
      .get(t.from())
      .exists(outgoing => outgoing contains t)
  }

  def addState(s: State): AutomatonBuilder = {
    _autStates += s
    this
  }

  def addStates(statesToAdd: Iterable[State]): AutomatonBuilder = {
    _autStates ++= statesToAdd
    this
  }

  private def assertHasState(state: State): Unit =
    assert(
      _autStates contains state,
      s"$state does not exist."
    )

  def setInitial(newInitialState: State): AutomatonBuilder = {
    assertHasState(newInitialState)
    _initial = Some(newInitialState)
    forward setReachable newInitialState
    this
  }

  def setAccepting(acceptingStates: State*): AutomatonBuilder = {
    assert(acceptingStates forall (_autStates(_)))
    _accepting ++= acceptingStates
    acceptingStates.foreach(backward.setReachable)
    this
  }

  @deprecated("Please don't use for performance reasons")
  def setNotAccepting(notAcceptingStates: State*): AutomatonBuilder = {
    assert(notAcceptingStates forall (_autStates(_)))
    // We need to reconstruct backwards reachability from scratch
    backward = new IncrementallyReachable[State]
    _accepting --= notAcceptingStates
    _accepting.foreach(s => backward.setReachable(s))
    _outgoingTransitions.values.flatten
      .foreach(t => backward.canGo(t.to(), t.from()))
    this
  }

  def addTransition(t: Transition): AutomatonBuilder = {
    trace(s"add transition $t on $name")()
    assert((_autStates contains t.from()) && (_autStates contains t.to()))

    _outgoingTransitions = _outgoingTransitions.updatedWith(t.from()) {
      case None                   => Some(SortedSet(t))
      case Some(previousOutgoing) => Some(previousOutgoing + t)
    }

    forward.canGo(t.from(), t.to())
    backward.canGo(t.to(), t.from())
    this
  }

  private def stateIsLive(s: State): Boolean =
    forward.isReachable(s) && backward.isReachable(s)

  def getAutomaton(): Automaton = {
    assert(_initial.isDefined, "Must have initial state!")
    val initial = _initial.get

    if (!backward.isReachable(initial)) return trace("getAutomaton")(REJECT_ALL)

    val reachableTransitions =
      _outgoingTransitions.view
        .filterKeys(stateIsLive) // Only from live states
        .mapValues(ts => ts.filter(t => stateIsLive(t.to()))) // Only to live states
        .toMap

    new Aut(initial, _accepting, reachableTransitions, _autStates, name)
  }
}

sealed private class Aut(
    initial: State,
    accepting: Set[State],
    _transitions: Map[State, SortedSet[Transition]],
    override val states: SortedSet[State],
    _name: Option[String]
) extends Automaton {
  override def transitionsFrom(from: State): Seq[Transition] =
    _transitions.getOrElse(from, Seq()).toSeq
  override val initialState: State = initial
  override def isAccept(s: State): Boolean = accepting contains s
  override def name(): String = _name.getOrElse(super.name)
}

object AutomatonBuilder {
  def apply() = new AutomatonBuilder()
  def apply(aut: Automaton): AutomatonBuilder = {
    val builder = new AutomatonBuilder()
    builder.addStates(aut.states)
    builder.setInitial(aut.initialState)
    builder.setAccepting(aut.states.filter(aut.isAccept).toSeq: _*)
    aut.transitions.foreach(builder.addTransition)
    builder
  }
}

@inline
sealed private class IncrementallyReachable[S] {
  private val reachable = mutable.Set[S]()
  private val notYetReachable = mutable.HashMap[S, mutable.Set[S]]()

  private def addMove(from: S, to: S): Unit =
    notYetReachable.getOrElseUpdate(from, mutable.Set[S]()).add(to)

  // Remove everything reachable from at, and insert those into reachable
  private def startReachabilityTrace(at: S): Unit = {
    val todo = mutable.Queue[S](at)

    while (todo.nonEmpty) {
      val current = todo.dequeue()
//      assert(
//        !reachable.contains(current),
//        s"Invariant violation: reachability re-discovered state $current!"
//      )
      reachable add current

      val previouslyUnreachableNeighbours = notYetReachable
        .remove(current)
        .getOrElse(mutable.Set.empty)
        .diff(reachable)
      todo enqueueAll previouslyUnreachableNeighbours
    }
  }
  def setReachable(reachableState: S): Unit =
    if (!reachable.contains(reachableState))
      startReachabilityTrace(reachableState)
  def canGo(from: S, to: S): Unit =
    if (reachable contains from) this setReachable to else addMove(from, to)
  def isReachable(s: S): Boolean = reachable contains s
}
