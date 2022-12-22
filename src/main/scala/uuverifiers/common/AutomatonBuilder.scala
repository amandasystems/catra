package uuverifiers.common

import collection.mutable.ArrayBuffer
import scala.collection.{SortedSet, mutable}

class AutomatonBuilder extends Tracing {
  private var _autStates = SortedSet[State]()
  private var _outgoingTransitions = Map[State, SortedSet[Transition]]()
  private var _initial: Option[State] = None
  private var _accepting = Set[State]()
  private var forwardReachable = Set[State]()
  private var backwardReachable = Set[State]()
  private var name: Option[String] = None

  /**
   * Transitively set s and any state reachable when starting in s as reachable.
   *
   * @param s The state to set reachable
   */
  private def setFwdReachable(s: State) =
    trace(s"setting forward reachable $s") {
      var todo = List(s)

      def markReachable(s: State): Unit = {
        forwardReachable += s
      }
      def enqueue(s: State): Unit = trace(s"adding $s to queue") {
        todo = s :: todo
      }

      markReachable(s)

      while (todo.nonEmpty) {
        val current = todo.head
        todo = todo.tail

        for (t <- _outgoingTransitions.getOrElse(current, Seq())) {
          val targetSeenBefore = forwardReachable contains t.to()
          if (!targetSeenBefore) {
            enqueue(t.to())
            markReachable(t.to())
          }
        }
      }
      forwardReachable
    }

  /**
   * Start a backwards reachability search here, populating
   * backwardsReachable.
   *
   * @param startingState
   */
  private def startBwdReachability(startingState: State) =
    trace(s"start backwardsReachable $startingState") {
      val reachedFrom = new mutable.HashMap[State, ArrayBuffer[State]]
      var todo = List[State](startingState)

      def enqueue(s: State): Unit = trace(s"adding $s to queue") {
        todo = s :: todo
      }

      def dequeue() = {
        val next = todo.head
        todo = todo.tail
        next
      }

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
        val next = dequeue()

        for (sources <- reachedFrom get next)
          for (source <- sources) {
            val sourceSeenBefore = backwardReachable contains source
            if (!sourceSeenBefore) {
              markReachable(source)
              enqueue(source)
            }
          }
      }

      backwardReachable
    }

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
    forwardReachable = Set() // All states are now unreachable...
    _initial = Some(newInitialState)
    setFwdReachable(newInitialState) //...until we recompute.
    this
  }

  def setAccepting(acceptingStates: State*): AutomatonBuilder = {
    assert(acceptingStates forall (_autStates(_)))
    _accepting ++= acceptingStates
    acceptingStates.foreach(s => startBwdReachability(s))
    this
  }

  def setNotAccepting(notAcceptingStates: State*): AutomatonBuilder = {
    assert(notAcceptingStates forall (_autStates(_)))
    backwardReachable = Set()
    _accepting --= notAcceptingStates
    _accepting.foreach(s => startBwdReachability(s))
    this
  }

  def addTransition(t: Transition): AutomatonBuilder = {
    trace(s"add transition $t on $name")()
    assert((_autStates contains t.from()) && (_autStates contains t.to()))

    _outgoingTransitions = _outgoingTransitions.updatedWith(t.from()) {
      case None                   => Some(SortedSet(t))
      case Some(previousOutgoing) => Some(previousOutgoing + t)
    }

    if (forwardReachable contains t.from()) {
      setFwdReachable(t.to())
    }

    if (backwardReachable contains t.to()) {
      startBwdReachability(t.from())
    }

    this
  }

  def getAutomaton(): Automaton = {
    assert(_initial.isDefined, "Must have initial state!")

    if (!_accepting.exists(forwardReachable contains _))
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
