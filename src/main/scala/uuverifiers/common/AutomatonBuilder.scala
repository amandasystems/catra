package uuverifiers.common

import collection.mutable.ArrayBuffer
import scala.collection.{SortedSet, mutable}

class AutomatonBuilder extends Tracing {
  private val _autStates = mutable.SortedSet[State]()
  private var _outgoingTransitions = Map[State, SortedSet[Transition]]()
  private var _initial: Option[State] = None
  private val _accepting = mutable.SortedSet[State]()
  private var forwardReachable = mutable.HashSet[State]()
  private val backwardReachable = mutable.HashSet[State]()
  private var name: Option[String] = None

  private def doUpdate(update: => Unit): AutomatonBuilder = {
    update
    this
  }

  /**
   * Transitively set s and any state reachable when starting in s as reachable.
   *
   * @param s The state to set reachable
   */
  private def setFwdReachable(s: State): Unit =
    trace(s"setting forward reachable $s") {
      val todo = mutable.Queue(s)

      def markReachable(s: State): Unit = {
        forwardReachable += s
      }

      markReachable(s)

      while (todo.nonEmpty) {
        val current = todo.dequeue()

        for (t <- _outgoingTransitions.getOrElse(current, Seq())) {
          val targetSeenBefore = forwardReachable contains t.to()
          if (!targetSeenBefore) {
            todo.enqueue(t.to())
            markReachable(t.to())
          }
        }
      }
    }

  /**
   * Start a backwards reachability search here, populating
   * backwardsReachable.
   */
  private def startBwdReachability(startingState: State): Unit =
    trace(s"start backwardsReachable $startingState") {
      val reachedFrom = new mutable.HashMap[State, ArrayBuffer[State]]
      val todo = mutable.Queue(startingState)

      def markReachable(s: State): Unit =
        trace(s"$s is backwards reachable") {
          backwardReachable += s
        }

      _outgoingTransitions.values.flatten
        .foreach(
          t => reachedFrom.getOrElseUpdate(t.to(), new ArrayBuffer) += t.from()
        )

      markReachable(startingState)

      while (todo.nonEmpty) {
        val next = todo.dequeue()

        for (sources <- reachedFrom get next)
          for (source <- sources) {
            val sourceSeenBefore = backwardReachable contains source
            if (!sourceSeenBefore) {
              markReachable(source)
              todo.enqueue(source)
            }
          }
      }
    }

  def nameIs(n: String): AutomatonBuilder = doUpdate {
    this.name = Some(n)
  }

  def containsState(s: State): Boolean = _autStates contains s

  def containsTransition(t: Transition): Boolean = {
    _outgoingTransitions
      .get(t.from())
      .exists(outgoing => outgoing contains t)
  }

  def addState(s: State): AutomatonBuilder = doUpdate {
    _autStates += s
  }

  def addStates(statesToAdd: Iterable[State]): AutomatonBuilder = doUpdate {
    _autStates ++= statesToAdd
  }

  private def assertHasState(state: State): Unit =
    assert(
      _autStates contains state,
      s"$state does not exist."
    )

  def setInitial(newInitialState: State): AutomatonBuilder = doUpdate {
    assertHasState(newInitialState)
    forwardReachable = mutable.HashSet() // All states are now unreachable...
    _initial = Some(newInitialState)
    setFwdReachable(newInitialState) //...until we recompute.
  }

  def setAccepting(acceptingStates: State*): AutomatonBuilder = doUpdate {
    assert(acceptingStates forall (_autStates(_)))
    _accepting ++= acceptingStates
  }

  def setNotAccepting(notAcceptingStates: State*): AutomatonBuilder = doUpdate {
    assert(notAcceptingStates forall (_autStates(_)))
    _accepting --= notAcceptingStates
  }

  def addTransition(t: Transition): AutomatonBuilder = doUpdate {
    trace(s"add transition $t on $name")()
    assert((_autStates contains t.from()) && (_autStates contains t.to()))

    _outgoingTransitions = _outgoingTransitions.updatedWith(t.from()) {
      case None                   => Some(SortedSet(t))
      case Some(previousOutgoing) => Some(previousOutgoing + t)
    }

    if (forwardReachable contains t.from()) {
      setFwdReachable(t.to())
    }

  }

  def getAutomaton(): Automaton = {
    assert(_initial.isDefined, "Must have initial state!")

    if (!_accepting.exists(forwardReachable contains _))
      return trace("AutomatonBuilder::getAutomaton")(REJECT_ALL)

    _accepting.foreach(startBwdReachability)

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

    new Aut(
      _initial.get,
      _accepting.toSet,
      reachableTransitions,
      _autStates,
      name
    )
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
