package uuverifiers.parikh_theory

import collection.mutable.{HashMap, ArrayBuffer}

/**
 An automaton as far as the Parikh Theory is concerned.
 */
trait Automaton extends Tracing {

  type State
  type Label

  /**
   * Iterate over automaton states
   */
  def states: Iterable[State]

  /**
   * Transitions are just tuples of from, label, to
   */
  type Transition = (State, Label, State)

  /**
   * Given a state, iterate over all outgoing transitions
   */
  def outgoingTransitions(from: State): Iterator[(State, Label)]

  /**
   * The unique initial state
   */
  val initialState: State

  /**
   * Test if state is accepting
   */
  def isAccept(s: State): Boolean

  /// Derived methods ///

  /**
   *  True if the automaton accepts no string, false otherwise.
   */
  def isEmpty(): Boolean = {

    val acceptingStates = states.filter(isAccept).toSet

    acceptingStates.isEmpty || {
      val g = toGraph
      val unreachableStates = g.unreachableFrom(initialState).toSet
      (acceptingStates diff unreachableStates).isEmpty
    }
  }

  /**
   * Filter an automaton, producing a new automaton with a subset of its
   * previous edges, as defined by a predicate.
   */
  def filterTransitions(
      keepEdge: Transition => Boolean
  ): Automaton = {
    val filteredBuilder = AutomatonBuilder[State, Label]()

    this.transitions.filter(keepEdge).foreach {
      case (from, label, to) =>
        val involvedStates = Seq(from, to)
        filteredBuilder
          .addStates(involvedStates)
          .addTransition(from, label, to)

        val acceptingStates = involvedStates.filter(isAccept).toSeq
        filteredBuilder.addStates(acceptingStates)
        acceptingStates.foreach(filteredBuilder setAccepting _)
    }

    if (filteredBuilder contains initialState)
      filteredBuilder.setInitial(initialState).getAutomaton()
    else REJECT_ALL
  }

  // TODO write a transitionsBreadthFirst, use for branching

  /**
   * Iterate over all transitions
   */
  def transitions: Iterator[Transition] =
    for (s1 <- states.iterator; (s2, lbl) <- outgoingTransitions(s1))
      yield (s1, lbl, s2)

  class AutomatonGraph(
      private val _states: Iterable[State],
      private val _transitions: Iterable[Transition]
  ) extends Graphable[State, Label] {

    def allNodes() = _states.toSeq
    def edges() = _transitions.toSeq
    def transitionsFrom(node: State) =
      outgoingTransitions(node).map(t => (node, t._2, t._1)).toSeq

    // FIXME this is ugly we should *not* change type
    def subgraph(selectedNodes: Set[State]): Graphable[State, Label] =
      this.dropEdges(Set()).subgraph(selectedNodes)
    def dropEdges(edgesToDrop: Set[(State, Label, State)]) = {
      new MapGraph(edges().toSet &~ edgesToDrop)
    }

    def addEdges(edgesToAdd: Iterable[(State, Label, State)]) = {
      val selectedEdges: Set[(State, Label, State)] = this
        .edges()
        .toSet ++ edgesToAdd
      new MapGraph(selectedEdges.toSeq)
    }
  }

  // Note: labels must be of same type, but we can't easily convince Scala of
  // that.
  private def transitionsWithOverlappingLabels[S, L](
      left: Iterator[(State, Label)],
      right: Iterator[(S, L)]
  ): Iterator[(Label, State, S)] = {

    // This will fail if labels have incompatible type
    val labelToRightStates = right
      .map { case (s, l) => l.asInstanceOf[Label] -> s }
      .toSeq
      .groupBy(_._1)
      .view
      .mapValues(_.map(_._2).toSet)

    left.filter(labelToRightStates contains _._2).flatMap {
      case (leftState, l) =>
        labelToRightStates(l).map(rightState => (l, leftState, rightState))
    }

  }

  // Type system breaks if not toSeq here...for whatever reason
  lazy val toGraph = new AutomatonGraph(this.states, this.transitions.toSeq)

  private def stateToProductState(s: Any): ProductState[State] = s match {
    case st: ProductState[State] => st
    case st: State               => ProductState(Set(st))
  }

  /**
   * Compute the product of two automata, somewhat smallish.
   */
  def &&&[A <: Automaton](that: A): Automaton =
    trace(s"${this} &&& ${that} gives") { this.productWithSources(that)._1 }

  /**
   * Compute the product of two automata, returning a mapping from the product's
    transitions to the term's.
    **/
  def productWithSources[A <: Automaton](
      that: A
  ): (
      Automaton,
      Map[
        (Any, Any, Any),
        Seq[(ProductState[State], Label, ProductState[State])]
      ]
  ) = {

    val termToProductEdges =
      HashMap[
        (Any, Label, Any),
        ArrayBuffer[(ProductState[State], Label, ProductState[State])]
      ]()

    val productBuilder = AutomatonBuilder[ProductState[State], Label]()
    val visitedStates = HashMap[(State, that.State), ProductState[State]]()
    var statesToVisit = List[(this.State, that.State)]()

    def newStateDiscovered(left: this.State, right: that.State) =
      trace("newStateDiscovered") {
        val productState
            : ProductState[State] = stateToProductState(left) union stateToProductState(
          right
        )
        visitedStates += ((left, right) -> productState)
        statesToVisit = (left, right) +: statesToVisit
        productBuilder.addStates(Seq(productState))

        if ((this isAccept left) && (that isAccept right)) {
          productBuilder setAccepting trace("product accepting")(productState)
        }

        productState
      }

    val initial = trace("product initial state")(
      newStateDiscovered(this.initialState, that.initialState)
    )
    productBuilder.setInitial(initial)

    while (!statesToVisit.isEmpty) {
      val (nextTarget +: rest) = statesToVisit
      statesToVisit = rest

      val (thisSourceState, thatSourceState) = nextTarget
      val fromProductState = visitedStates((thisSourceState, thatSourceState))
      val overlappingTransitions = trace(
        s"overlappingTransitions from ${thisSourceState}/${thatSourceState}"
      )(
        transitionsWithOverlappingLabels(
          this outgoingTransitions thisSourceState,
          that outgoingTransitions thatSourceState
        ).toSeq
      )
      overlappingTransitions.foreach {
        case (label, leftTo, rightTo) =>
          val toProductState =
            if (!(visitedStates contains ((leftTo, rightTo))))
              newStateDiscovered(leftTo, rightTo)
            else visitedStates((leftTo, rightTo))

          productBuilder.addTransition(fromProductState, label, toProductState)

          val productTransition = trace("productTransition")(
            (fromProductState, label, toProductState)
          )

          termToProductEdges.getOrElseUpdate(
            (thisSourceState, label, leftTo),
            ArrayBuffer()
          ) += productTransition

          termToProductEdges.getOrElseUpdate(
            (thatSourceState, label, rightTo),
            ArrayBuffer()
          ) += productTransition

          trace("termtoProductEdges")(termToProductEdges)
      }
    }

    (productBuilder.getAutomaton(), termToProductEdges.mapValues(_.toSeq).toMap)
  }
}

// TODO keep track of reachable states and make sure we return REJECT_ALL if unreachable.
// TODO build minimally
class AutomatonBuilder[S, L] extends Tracing {
  private var _autStates = Set[S]()
  private var _transitions = Set[(S, L, S)]()
  private var _initial: Option[S] = None
  private var _accepting = Set[S]()

  def contains(s: S) = _autStates contains s

  def contains(t: (S, L, S)) = _transitions contains t

  def addStates(statesToAdd: Seq[S]): AutomatonBuilder[S, L] = {
    _autStates ++= statesToAdd
    this
  }

  def setInitial(newInitialState: S): AutomatonBuilder[S, L] = {
    assert(_autStates contains newInitialState)
    _initial = Some(newInitialState)
    this
  }

  def setAccepting(acceptingStates: S*): AutomatonBuilder[S, L] = {
    assert(acceptingStates forall (_autStates(_)))
    _accepting ++= acceptingStates
    this
  }

  def addTransition(from: S, label: L, to: S): AutomatonBuilder[S, L] = {
    assert((_autStates contains from) && (_autStates contains to))
    _transitions += ((from, label, to))
    this
  }

  def getAutomaton(): Automaton = {
    assert(_initial != None)

    if (_accepting.isEmpty)
      return trace("AutomatonBuilder::getAutomaton")(REJECT_ALL)

    object Aut extends Automaton {
      type State = S
      type Label = L

      override def toString() =
        this.transitions
          .map { case (from, label, to) => s"${from} -(${label})-> ${to}" }
          .mkString(", ")

      override val initialState = _initial.get
      override def isAccept(s: State) = _accepting contains s
      override def outgoingTransitions(from: State) =
        _transitions
          .filter { case (thatFrom, _, _) => thatFrom == from }
          .map {
            case (_, label, to) => (to, label)
          }
          .iterator
      override val states = _autStates
    }

    Aut
  }
}

object AutomatonBuilder {
  def apply[S, L]() = new AutomatonBuilder[S, L]()
}

/**
 * A ProductState is a state derived from a product of one or more automata,
 * possibly transitively.
 */
sealed case class ProductState[S](baseStates: Set[S]) extends Iterable[S] {
  def union(that: ProductState[S]): ProductState[S] =
    ProductState(this.baseStates ++ that)
  def union(that: S): ProductState[S] = ProductState(this.baseStates + that)
  override def iterator: Iterator[S] = baseStates.iterator
  override def toString() = "ProudctState(" + baseStates.mkString(" & ") + ")"

}

object REJECT_ALL extends Automaton {
  type State = Unit
  type Label = Unit

  override val initialState = None
  override def isAccept(_s: Unit) = false
  override def outgoingTransitions(_from: Unit) = Iterator.empty
  override def states = Seq.empty
}
