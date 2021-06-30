package uuverifiers.parikh_theory

import collection.mutable.{HashMap, ArrayBuffer}
import scala.language.implicitConversions

object AutomataTypes {
  type State = Int
  type Label = SymbolicLabel

  /**
   * Transitions are just tuples of from, label, to
   */
  type Transition = (State, SymbolicLabel, State)

  type Origin = TermOrigin.TermOrigin

  /**
   * A type to track term transitions to their resulting transitions in a product
   */
  type ProductTransitionMap = Map[(Origin, Transition), Seq[Transition]]

  /**
   * A type to trace a product state to its origin term states
   */
  type ProductStateMap = Map[State, (State, State)]
}

/**
 An automaton as far as the Parikh Theory is concerned.
 */
trait Automaton
    extends Tracing
    with Graphable[AutomataTypes.State, AutomataTypes.Label] {
  import AutomataTypes._

  /**
   * Iterate over automaton states
   */
  def states: Iterable[State]

  /**
   * Given a state, iterate over all outgoing transitions
   */
  def outgoingTransitions(from: State): Iterator[(State, SymbolicLabel)]

  /**
   * The unique initial state
   */
  val initialState: State

  /**
   * Test if state is accepting
   */
  def isAccept(s: State): Boolean

  /// Derived methods ///

  def ++(that: Automaton) = {
    val builder = AutomatonBuilder(this)
    // add all states of that, incremented
    // make all this's accepting states not accepting
    // in every accepting state, paste a copy of that
    // set all of that's accepting states to accepting
    builder.getAutomaton()
    ???
  }

  def |||(that: Automaton) = {
    // make a new initial state
    // make a new accepting state
    // increment the states of this by two and that by length + 2
    // add all edges from this and that
    // all accepting states gets an edge to the new accepting state
    // the initial sate gets an edge to this and that's accepting states each
    ???
  }

  // FIXME this will not be true once we allow symbolic labels!
  def alphabet(): Iterator[SymbolicLabel] =
    transitions.map {
      case (_, label, _) => label
    }

  /**
   *  True if the automaton accepts no string, false otherwise.
   */
  def isEmpty(): Boolean = {

    val acceptingStates = states.filter(isAccept).toSet

    acceptingStates.isEmpty || {
      val unreachableStates = this.unreachableFrom(initialState)
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
    val filteredBuilder = AutomatonBuilder()

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

  /**
   * Iterate over all transitions
   */
  def transitions: Iterator[Transition] =
    for (s1 <- states.iterator; (s2, lbl) <- outgoingTransitions(s1))
      yield (s1, lbl, s2)

  def allNodes() = states.toSeq
  def edges() = transitions.toSeq
  def transitionsFrom(node: State) =
    outgoingTransitions(node).map(t => (node, t._2, t._1)).toSeq

  def subgraph(selectedNodes: Set[State]): Automaton = {
    val builder = AutomatonBuilder()
    val statesToKeep = states.filter(selectedNodes.contains)
    builder.addStates(statesToKeep)
    if (selectedNodes contains initialState) {
      builder.setInitial(initialState)
      statesToKeep.filter(isAccept).foreach(builder.setAccepting(_))
    }
    builder.getAutomaton()
  }

  def dropEdges(edgesToDrop: Set[Transition]) =
    filterTransitions(!edgesToDrop.contains(_))

  def addEdges(edgesToAdd: Iterable[Transition]) = {
    val builder = AutomatonBuilder(this)
    edgesToAdd.foreach {
      case (from, label, to) => builder.addTransition(from, label, to)
    }
    builder.getAutomaton()
  }

  // Note: labels must be of same type, but we can't easily convince Scala of
  // that.
  private def transitionsWithOverlappingLabels(
      left: Iterator[(State, SymbolicLabel)],
      right: Iterator[(State, SymbolicLabel)]
  ): Iterator[(SymbolicLabel, State, State)] = {

    // This will fail if labels have incompatible type
    val labelToRightStates = right
      .map { case (s, l) => l -> s }
      .toSeq
      .groupBy(_._1)
      .view
      .mapValues(_.map(_._2).toSet)

    left.filter(labelToRightStates contains _._2).flatMap {
      case (leftState, l) =>
        labelToRightStates(l).map(rightState => (l, leftState, rightState))
    }

  }

  /**
   * Compute the product of two automata, somewhat smallish.
   */
  def &&&(that: Automaton): Automaton =
    trace(s"${this} &&& ${that} gives") {
      this.productWithSources(that).product
    }

  /**
   * Compute the product of two automata, returning a mapping from the product's
    transitions to the term's.
    **/
  def productWithSources(that: Automaton): AnnotatedProduct = {
    // NOTE We have to tag keys with the origin of the term, since there is no
    // guarantee that transitions are unique between automata.
    val termToProductEdges =
      HashMap[(Origin, Transition), ArrayBuffer[Transition]]()
    val productBuilder = AutomatonBuilder()
    // this, that to product
    val knownProductStates = HashMap[(State, State), State]()
    var statesToVisit = List[(State, State)]()

    def newStateDiscovered(left: State, right: State) =
      trace("newStateDiscovered") {
        val productState = productBuilder.getNewState()
        knownProductStates += ((left, right) -> productState)
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
      val fromProductState = knownProductStates(
        (thisSourceState, thatSourceState)
      )
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
            if (!(knownProductStates contains ((leftTo, rightTo))))
              newStateDiscovered(leftTo, rightTo)
            else knownProductStates((leftTo, rightTo))

          productBuilder.addTransition(fromProductState, label, toProductState)

          val productTransition = trace("productTransition")(
            (fromProductState, label, toProductState)
          )

          termToProductEdges.getOrElseUpdate(
            (TermOrigin.Left, (thisSourceState, label, leftTo)),
            ArrayBuffer()
          ) += productTransition

          termToProductEdges.getOrElseUpdate(
            (TermOrigin.Right, (thatSourceState, label, rightTo)),
            ArrayBuffer()
          ) += productTransition

          trace("termtoProductEdges")(termToProductEdges)
      }
    }

    AnnotatedProduct(
      productBuilder.getAutomaton(),
      termToProductEdges.mapValues(_.toSeq).toMap,
      knownProductStates.toMap.map(_.swap)
    )
  }
}

// TODO keep track of reachable states and make sure we return REJECT_ALL if unreachable.
// TODO build minimally
class AutomatonBuilder extends Tracing {
  import AutomataTypes._

  private var _autStates = Set[State]()
  private var _transitions = Set[Transition]()
  private var _initial: Option[State] = None
  private var _accepting = Set[State]()

  def contains(s: State) = _autStates contains s

  def contains(t: Transition) = _transitions contains t

  def addStates(statesToAdd: Iterable[State]): AutomatonBuilder = {
    _autStates ++= statesToAdd
    this
  }

  def getNewState(): State = {
    val newState = if (!_autStates.isEmpty) _autStates.max + 1 else 0
    addStates(Seq(newState))
    newState
  }

  def setInitial(newInitialState: State): AutomatonBuilder = {
    assert(_autStates contains newInitialState)
    _initial = Some(newInitialState)
    this
  }

  def setAccepting(acceptingStates: State*) = {
    assert(acceptingStates forall (_autStates(_)))
    _accepting ++= acceptingStates
    this
  }

  def addTransition(from: State, label: Label, to: State) = {
    assert((_autStates contains from) && (_autStates contains to))
    _transitions += ((from, label, to))
    this
  }

  def getAutomaton(): Automaton = {
    assert(_initial != None)

    if (_accepting.isEmpty)
      return trace("AutomatonBuilder::getAutomaton")(REJECT_ALL)

    object Aut extends Automaton {
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
  def apply() = new AutomatonBuilder()
  def apply(aut: Automaton) = {
    val builder = new AutomatonBuilder()
    builder.setInitial(aut.initialState)
    builder.addStates(aut.states)
    builder.setAccepting(aut.states.filter(aut.isAccept).toSeq: _*)
    aut.transitions.foreach {
      case (from, label, to) => builder.addTransition(from, label, to)
    }
    builder
  }
}

object REJECT_ALL extends Automaton {
  override val initialState = 0
  override def isAccept(_s: AutomataTypes.State) = false
  override def outgoingTransitions(_from: AutomataTypes.State) = Iterator.empty
  override def states = Seq.empty
  override def isEmpty() = true
}

sealed abstract class SymbolicLabel
    extends Product
    with Serializable
    with Ordered[SymbolicLabel] {
  def subtract(that: SymbolicLabel): SymbolicLabel
  def intersect(that: SymbolicLabel): SymbolicLabel
  def isEmpty(): Boolean
  def overlaps(that: SymbolicLabel) = !this.intersect(that).isEmpty()
  def upperBoundExclusive(): Option[Char]
  override def compare(that: SymbolicLabel) = {
    (this.upperBoundExclusive(), that.upperBoundExclusive()) match {
      case (None, None)    => 0
      case (None, Some(_)) => 1
      case (Some(_), None) => -1
      case (Some(thisBound), Some(thatBound)) =>
        java.lang.Character.compare(thisBound, thatBound)
    }
  }
}

object SymbolicLabel {
  def apply() = NoChar
  def apply(c: Char) = SingleChar(c)
  def apply(fromInclusive: Char, toInclusive: Char) =
    toInclusive - fromInclusive match {
      case diff if diff < 0 => NoChar
      case diff if diff > 0 => CharRange(fromInclusive, toInclusive)
      case _                => SingleChar(fromInclusive)
    }

  final case class SingleChar(c: Char) extends SymbolicLabel {
    override def subtract(that: SymbolicLabel) = that match {
      case NoChar          => this
      case AnyChar         => NoChar
      case SingleChar(`c`) => NoChar
      case SingleChar(_)   => this
      case CharRange(from, toInclusive) if c <= toInclusive && from <= c =>
        NoChar
      case CharRange(_, _) => this
      // NOTE: this could be compactified with a final catch-all case, but I
      // avoided that in order to keep this safe against future
      // refactorings. --Amanda
    }
    override def overlaps(that: SymbolicLabel) = ???
    override def intersect(that: SymbolicLabel) = ???
    override def isEmpty() = false
    override def upperBoundExclusive() = Some((c + 1).toChar)

  }
  final case object AnyChar extends SymbolicLabel {
    override def overlaps(that: SymbolicLabel) = true
    override def intersect(that: SymbolicLabel) = that
    override def isEmpty() = false
    override def subtract(that: SymbolicLabel) = ???
    override def upperBoundExclusive() = None
  }
  final case object NoChar extends SymbolicLabel {
    override def overlaps(that: SymbolicLabel) = false
    override def intersect(that: SymbolicLabel) = this
    override def isEmpty() = true
    override def subtract(that: SymbolicLabel) = this
    override def upperBoundExclusive() = Some(0.toChar)
  }
  final case class CharRange(from: Char, toInclusive: Char)
      extends SymbolicLabel {
    override def subtract(that: SymbolicLabel) = ???
    override def overlaps(that: SymbolicLabel) = ???
    override def intersect(that: SymbolicLabel) = ???
    override def isEmpty() = false
    override def upperBoundExclusive() = Some((toInclusive + 1).toChar)
  }
}

object SymbolicLabelConversions {
  implicit def charToSymbolicLabel(c: Char): SymbolicLabel = SymbolicLabel(c)
}

/**
 * A container to store the origins of states and transitions from a product of
 * automata.
 *
 * @param product
 * @param termTransitionToProductTransitions
 * @param productStateToTermStates
 */
sealed case class AnnotatedProduct(
    val product: Automaton,
    val termTransitionToProductTransitions: AutomataTypes.ProductTransitionMap,
    val productStateToTermStates: AutomataTypes.ProductStateMap
) {

  def originOf(productState: AutomataTypes.State) =
    productStateToTermStates(productState)

  def resultsOf(
      leftOrRight: TermOrigin.TermOrigin
  )(transition: AutomataTypes.Transition) =
    termTransitionToProductTransitions.get((leftOrRight, transition))
}

object TermOrigin extends Enumeration {
  type TermOrigin = Value
  val Left, Right = Value
}
