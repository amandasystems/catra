package uuverifiers.common

import collection.mutable.ArrayBuffer
import scala.collection.{SortedSet, mutable}

class AutomatonBuilder extends Tracing {
  private var _autStates = SortedSet[State]()
  private var _outgoingTransitions = Map[State, SortedSet[Transition]]()
  private var _initial: Option[State] = None
  private var _accepting = Set[State]()
  private var forwardReachable = mutable.HashSet[State]()
  private var name: Option[String] = None

  /**
   * Transitively set s and any state reachable when starting in s as reachable.
   *
   * @param s The state to set reachable
   */
  private def setFwdReachable(s: State): mutable.HashSet[State] =
    ClosureComputation.computeClosure(
      startingFrom = Set(s),
      seen = forwardReachable,
      findMoreFrom =
        (s: State) => _outgoingTransitions.getOrElse(s, Seq()).map(_.to())
    )

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
    forwardReachable = mutable.HashSet() // All states are now unreachable...
    _initial = Some(newInitialState)
    setFwdReachable(newInitialState) //...until we recompute.
    this
  }

  def setAccepting(acceptingStates: State*): AutomatonBuilder = {
    assert(acceptingStates forall (_autStates(_)))
    _accepting ++= acceptingStates
    this
  }

  def setNotAccepting(notAcceptingStates: State*): AutomatonBuilder = {
    assert(notAcceptingStates forall (_autStates(_)))
    _accepting --= notAcceptingStates
    this
  }

  def addTransition(t: Transition): AutomatonBuilder = {
    trace(s"add transition $t on $name")(_outgoingTransitions.size)
    assert((_autStates contains t.from()) && (_autStates contains t.to()))

    _outgoingTransitions = _outgoingTransitions.updatedWith(t.from()) {
      case None                   => Some(SortedSet(t))
      case Some(previousOutgoing) => Some(previousOutgoing + t)
    }

    if (forwardReachable contains t.from()) {
      setFwdReachable(t.to())
    }

    this
  }

  def getAutomaton(): Automaton = {
    assert(_initial.isDefined, "Must have initial state!")

    if (!_accepting.exists(forwardReachable contains _))
      return trace("AutomatonBuilder::getAutomaton")(REJECT_ALL)

    val backwardReachable = {
      val transitionsReversed =
        _outgoingTransitions.values.flatten.groupMap(_.to())(_.from())

      ClosureComputation.computeClosure(
        startingFrom = _accepting,
        findMoreFrom = (s: State) => transitionsReversed.getOrElse(s, Seq())
      )
    }

    if (!(backwardReachable contains _initial.get))
      return trace("AutomatonBuilder::getAutomaton")(REJECT_ALL)

    // Ignore transitions into and from dead states (unreachable, or where no
    // path leads on to an accepting state)
    val reachableTransitions =
      _outgoingTransitions.view
        .filterKeys(
          s => (forwardReachable contains s) && (backwardReachable contains s)
        )
        .mapValues(ts => ts.filter(backwardReachable contains _.to()))
        .toMap

    new Aut(_initial.get, _accepting, reachableTransitions, _autStates, name)
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
