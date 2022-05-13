package uuverifiers.common
import EdgeWrapper._

import collection.mutable.{ArrayBuffer, HashMap}
import scala.collection.mutable

class AutomatonBuilder extends Tracing {
  import AutomataTypes._

  private var _autStates = Set[State]()
  private var _outgoingTransitions = Map[State, Set[Transition]]()
  private var _initial: Option[State] = None
  private var _accepting = Set[State]()
  private var forwardReachable = Set[State]()
  private var backwardReachable = Set[State]()

  /**
   * Transitively set s and any state reachable when starting in s as reachable.
   *
   * @param s The state to set reachable
   */
  private def setFwdReachable(s: State) =
    trace(s"setting forward reachable ${s}") {
      var todo = List(s)

      def markReachable(s: State): Unit = {
        forwardReachable += s
      }
      def enqueue(s: State) = trace(s"adding ${s} to queue") {
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
    trace(s"start backwardsReachable ${startingState}") {
      val reachedFrom = new mutable.HashMap[State, ArrayBuffer[State]]
      var todo = List[State](startingState)

      def enqueue(s: State): Unit = trace(s"adding ${s} to queue") {
        todo = s :: todo
      }

      def dequeue() = {
        val next = todo.head
        todo = todo.tail
        next
      }

      def markReachable(s: State): Unit = trace(s"${s} is backwards reachable") {
        backwardReachable += s
      }

      _outgoingTransitions
        .values
        .flatten
        .foreach(
          t => reachedFrom.getOrElseUpdate(t.to(), new ArrayBuffer) += t.from()
        )

      markReachable(startingState)

      while (!todo.isEmpty) {
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

  def containsState(s: State): Boolean = _autStates contains s

  def containsTransition(t: Transition): Boolean = {
    _outgoingTransitions
      .get(t.from()).exists(outgoing => outgoing contains t)
  }

  def addState(s: State): AutomatonBuilder = {
    _autStates += s
    this
  }

  def addStates(statesToAdd: Iterable[State]): AutomatonBuilder = {
    _autStates ++= statesToAdd
    this
  }

  private def assertHasState(state: State) =
    assert(
      _autStates contains state,
      s"${state} does not exist."
    )

  def getNewState(): State = {
    val newState =
      if (_autStates.nonEmpty) _autStates.max.successor() else IntState(0)
    addStates(Seq(newState))
    newState
  }

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

  def addTransition(from: State, label: Label, to: State): AutomatonBuilder =
    trace(s"add transition ${from} ${label} ${to}") {
      assert((_autStates contains from) && (_autStates contains to))
      val newTransition = (from, label, to)

      _outgoingTransitions = _outgoingTransitions.updatedWith(from) {
        case None                   => Some(Set(newTransition))
        case Some(previousOutgoing) => Some(previousOutgoing + newTransition)
      }

      if (forwardReachable contains from) {
        setFwdReachable(to)
      }

      if (backwardReachable contains to) {
        startBwdReachability(from)
      }

      this
    }

  def addTransition(t: Transition): AutomatonBuilder =
    this.addTransition(t.from(), t.label(), t.to())

  def getAutomaton(): Automaton = {
    assert(_initial != None, "Must have initial state!")

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

    object Aut extends Automaton {
      override val initialState = _initial.get
      override def isAccept(s: State) = _accepting contains s
      override def transitionsFrom(from: State) =
        reachableTransitions.getOrElse(from, Seq()).toSeq
      override val states = _autStates
    }

    Aut
  }
}

object AutomatonBuilder {
  def apply() = new AutomatonBuilder()
  def apply(aut: Automaton) = {
    val builder = new AutomatonBuilder()
    builder.addStates(aut.states)
    builder.setInitial(aut.initialState)
    builder.setAccepting(aut.states.filter(aut.isAccept).toSeq: _*)
    aut.transitions.foreach(builder.addTransition)
    builder
  }
}
