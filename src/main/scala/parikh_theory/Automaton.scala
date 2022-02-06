package uuverifiers.parikh_theory

import collection.mutable.{HashMap, ArrayBuffer, Queue}
import scala.language.implicitConversions
import EdgeWrapper._

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
    with Graphable[AutomataTypes.State, AutomataTypes.Label]
    with GraphvizDumper {
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

  def alphabet(): Iterator[Char] = {
    val min = transitions
      .flatMap(
        t =>
          t.label() match {
            case SymbolicLabel.AnyChar           => Seq(Char.MinValue)
            case SymbolicLabel.NoChar            => Seq()
            case SymbolicLabel.SingleChar(c)     => Seq(c)
            case SymbolicLabel.CharRange(low, _) => Seq(low)
          }
      )
      .min

    val max = transitions
      .flatMap(
        t =>
          t.label() match {
            case SymbolicLabel.AnyChar           => Seq(Char.MinValue)
            case SymbolicLabel.NoChar            => Seq()
            case SymbolicLabel.SingleChar(c)     => Seq(c)
            case SymbolicLabel.CharRange(low, _) => Seq(low)
          }
      )
      .max

    (min to max).iterator
  }

  def toDot() =
    toDot(
      transitionAnnotator = _.label().toString(),
      stateAnnotator = _.toString()
    )

  def toDot(
      transitionAnnotator: Transition => String,
      stateAnnotator: State => String
  ): String = {

    def quote(s: String) = "\"" + s + "\""

    val builder = new StringBuilder("digraph Automaton {")
    builder ++= "rankdir = LR;\n"
    builder ++= "initial [shape=plaintext,label=\"\"];\n"
    builder ++= s"initial -> ${initialState};\n" // Add an incoming edge to the initial state

    states.foreach { s =>
      val shape = if (isAccept(s)) "doublecircle" else "circle"
      val quotedState = quote(stateAnnotator(s))
      builder ++= s"${s} [shape=${shape},label=${quotedState}];\n"
      transitionsFrom(s).foreach {
        case t @ (from, _, to) =>
          val quotedLabel = quote(transitionAnnotator(t))
          builder ++= s"${from} -> ${to} [label=${quotedLabel}]\n"
      }
    }

    builder ++= "}\n"

    builder.toString()
  }

  // TODO maybe apply sorting to transitionsFrom here for Full Determinism
  def transitionsBreadthFirst() =
    this.startBFSFrom(initialState).flatMap(transitionsFrom)

  def fmtState(s: State): String = {
    val initialDecoration = if (s == initialState) "➡" else ""
    val acceptingAnnotation = if (isAccept(s)) s"🏆(${s})" else s"(${s})"
    s"${initialDecoration}${acceptingAnnotation}"
  }

  override def toString(): String = {
    "Automaton:\n" + states
      .map(fmtState)
      .mkString(", ") + "\n" + transitions.toSeq
      .groupBy(_._1)
      .map {
        case (state, outgoing) =>
          s"== ${fmtState(state)} ==\n" + outgoing
            .map {
              case (_, label, to) =>
                s"\t${label} → ${to}"
            }
            .mkString("\n") + "\n"
      }
      .mkString("\n")
  }

  // TODO move this into the graph trait
  def walkFrom(currentStates: Seq[State], c: Char): Seq[State] =
    trace(s"walkFrom(${currentStates})") {
      val applicableMoves =
        currentStates
          .flatMap(
            currentState =>
              transitionsFrom(currentState)
                .filter(_.label().contains(c))
          )
      applicableMoves.map(_.to())
    }

  /**
   * Run the automaton on an input.
   *
   * @param input
   * @return true if the automaton accepts input, false otherwise
   */
  def accepts(input: String): Boolean =
    input.toSeq.foldLeft(Seq(initialState))(walkFrom).exists(isAccept)

  def ++(that: Automaton) = {
    val builder = AutomatonBuilder(this)

    // No states from this are accepting anymore
    builder.setNotAccepting(states.filter(isAccept).toSeq: _*)

    states
      .filter(isAccept)
      .foreach(insertCopyOfThat(_))

    def insertCopyOfThat(startingFrom: State) = {
      // Make fresh copies of all states, except the initial one which we merge
      // with the insertion point.
      val thatStateMap = that.states
        .map(
          s =>
            (
              s,
              if (s == that.initialState) startingFrom
              else builder.getNewState()
            )
        )
        .toMap

      // Copy over the transitions modulo the state remapping
      that.transitions.foreach {
        case (from, label, to) =>
          builder.addTransition(thatStateMap(from), label, thatStateMap(to))
      }

      // Mark all copied states that were accepting as still accepting.
      builder.setAccepting(
        that.states.filter(that.isAccept).map(thatStateMap).toSeq: _*
      )

    }

    builder.getAutomaton()
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

  /**
   *  True if the automaton accepts no string, false otherwise.
   */
  lazy val isEmpty: Boolean = {
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
      case t @ (from, _, to) =>
        val involvedStates = Seq(from, to)
        filteredBuilder
          .addStates(involvedStates)
          .addTransitionTuple(t)

        val acceptingStates = involvedStates.filter(isAccept).toSeq
        filteredBuilder.addStates(acceptingStates)
        acceptingStates.foreach(filteredBuilder setAccepting _)
    }

    if (filteredBuilder containsState initialState)
      filteredBuilder.setInitial(initialState).getAutomaton()
    else REJECT_ALL
  }

  /**
   * Iterate over all transitions
   */
  lazy val transitions = transitionsBreadthFirst().toSeq

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
    edgesToAdd.foreach(builder.addTransitionTuple)
    builder.getAutomaton()
  }

  /**
   * Find or compute overlapping transitions based on labels. If there are no
   * overlaps, return an empty iterator. If labels overlap partially, the
   * overlap is returned.
   *
   * @param left to-label from the left automaton
   * @param right to-label from the right automaton
   * @return the computed label and corresponding states from the left and
   * right automaton respectively
   */
  private def transitionsWithOverlappingLabels(
      left: Iterator[(State, SymbolicLabel)],
      right: Iterator[(State, SymbolicLabel)]
  ): Seq[(SymbolicLabel, SymbolicLabel, SymbolicLabel, State, State)] = {
    // NOTE: by sorting both lists by alternating lower and upper bounds, the
    // search can be accelerated by skipping ranges that can never overlap.
    // NOTE: we need to revisit the lists so we store the results of the
    // iteration here.
    val leftValues = left.toSeq
    val rightValues = right.toSeq

    leftValues.flatMap {
      case (leftState, leftLabel) =>
        rightValues
          .map {
            case (rightState, rightLabel) =>
              (
                trace(s"${leftLabel} INTERSECT ${rightLabel}")(
                  leftLabel intersect rightLabel
                ),
                leftLabel,
                rightLabel,
                leftState,
                rightState
              )
          }
          .filter(!_._1.isEmpty())
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
    val statesToVisit = Queue[(State, State)]()

    def newStateDiscovered(left: State, right: State) =
      trace("newStateDiscovered") {
        val productState = productBuilder.getNewState()
        knownProductStates += ((left, right) -> productState)
        statesToVisit enqueue ((left, right))
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
      val nextTarget = statesToVisit.dequeue()

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
        case (newLabel, leftOldLabel, rightOldLabel, leftTo, rightTo) =>
          val toProductState =
            if (!(knownProductStates contains ((leftTo, rightTo))))
              newStateDiscovered(leftTo, rightTo)
            else knownProductStates((leftTo, rightTo))

          productBuilder.addTransition(
            fromProductState,
            newLabel,
            toProductState
          )

          val productTransition = trace("productTransition")(
            (fromProductState, newLabel, toProductState)
          )

          termToProductEdges.getOrElseUpdate(
            (TermOrigin.Left, (thisSourceState, leftOldLabel, leftTo)),
            ArrayBuffer()
          ) += productTransition

          termToProductEdges.getOrElseUpdate(
            (TermOrigin.Right, (thatSourceState, rightOldLabel, rightTo)),
            ArrayBuffer()
          ) += productTransition

          trace("termtoProductEdges")(termToProductEdges)
      }
    }

    AnnotatedProduct(
      productBuilder.getAutomaton(),
      termToProductEdges.view.mapValues(_.toSeq).toMap,
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

  def containsState(s: State) = _autStates contains s

  def containsTransition(t: Transition) = _transitions contains t

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
    val newState = if (!_autStates.isEmpty) _autStates.max + 1 else 0
    addStates(Seq(newState))
    newState
  }

  def setInitial(newInitialState: State): AutomatonBuilder = {
    assertHasState(newInitialState)
    _initial = Some(newInitialState)
    this
  }

  def setAccepting(acceptingStates: State*) = {
    assert(acceptingStates forall (_autStates(_)))
    _accepting ++= acceptingStates
    this
  }

  def setNotAccepting(notAcceptingStates: State*) = {
    assert(notAcceptingStates forall (_autStates(_)))
    _accepting --= notAcceptingStates
    this
  }

  def addTransition(from: State, label: Label, to: State) = {
    assert((_autStates contains from) && (_autStates contains to))
    _transitions += ((from, label, to))
    this
  }

  def addTransitionTuple(t: (State, Label, State)) =
    (this.addTransition _).tupled(t)

  def getAutomaton(): Automaton = {
    assert(_initial != None, "Must have initial state!")

    if (_accepting.isEmpty)
      return trace("AutomatonBuilder::getAutomaton")(REJECT_ALL)

    object Aut extends Automaton {
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
    builder.addStates(aut.states)
    builder.setInitial(aut.initialState)
    builder.setAccepting(aut.states.filter(aut.isAccept).toSeq: _*)
    aut.transitions.foreach(builder.addTransitionTuple)
    builder
  }
}

object REJECT_ALL extends Automaton {
  override val initialState = 0
  override def isAccept(_s: AutomataTypes.State) = false
  override def outgoingTransitions(_from: AutomataTypes.State) = Iterator.empty
  override def states = Seq.empty
  override lazy val isEmpty = true
}

sealed abstract class SymbolicLabel
    extends Product
    with Serializable
    with Ordered[SymbolicLabel] {
  def iterate(): Iterator[Char]
  def subtract(that: SymbolicLabel): SymbolicLabel
  def intersect(that: SymbolicLabel): SymbolicLabel
  def isEmpty(): Boolean
  def contains(ch: Char) = this.overlaps(SymbolicLabel.SingleChar(ch))
  def overlaps(that: SymbolicLabel) = !this.intersect(that).isEmpty()
  def upperBoundExclusive(): Option[Char]
  override def compare(that: SymbolicLabel) = {
    (this.upperBoundExclusive(), that.upperBoundExclusive()) match {
      case (None, None)                       => 0
      case (None, Some(_))                    => 1
      case (Some(_), None)                    => -1
      case (Some(thisBound), Some(thatBound)) => thisBound compareTo thatBound
    }
  }
}

object SymbolicLabel {
  // TODO do something better; only escape characters that are unprintable
  private def formatChar(c: Char): String =
    if (c.isLetterOrDigit) c.toString() else c.toInt.toString()
  def apply() = NoChar
  def apply(c: Char) = SingleChar(c)
  def apply(fromInclusive: Char, toInclusive: Char) =
    (fromInclusive, toInclusive) match {
      case _ if fromInclusive > toInclusive  => NoChar
      case _ if fromInclusive == toInclusive => SingleChar(fromInclusive)
      case _                                 => CharRange(fromInclusive, toInclusive)
    }

  final case object NoChar extends SymbolicLabel {
    override def overlaps(that: SymbolicLabel) = false
    override def intersect(that: SymbolicLabel) = this
    override def isEmpty() = true
    override def subtract(that: SymbolicLabel) = this
    override def upperBoundExclusive() = Some(0.toChar)
    override def iterate() = Iterator()
    override def toString() = "∅"
  }

  final case class SingleChar(c: Char) extends SymbolicLabel with Tracing {
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

    override def intersect(that: SymbolicLabel) =
      trace(s"${this} ∩ ${that}") {
        that match {
          case AnyChar => this // Redundant but OK
          case SingleChar(otherChar) =>
            if (otherChar == this.c) this else NoChar
          case CharRange(lower, upper) =>
            if (c >= lower && c <= upper) this else NoChar
          case NoChar => NoChar
        }
      }
    override def isEmpty() = false
    override def upperBoundExclusive() = Some((c + 1).toChar)
    override def iterate() = Iterator(c)
    override def toString() = formatChar(c)

  }

  final case class CharRange(from: Char, toInclusive: Char)
      extends SymbolicLabel
      with Tracing {
    override def subtract(that: SymbolicLabel) = ???
    override def intersect(that: SymbolicLabel): SymbolicLabel =
      trace(s"${this} INTERSECTS ${that}") {
        that match {
          case CharRange(thatFrom, thatToInclusive) =>
            SymbolicLabel(thatFrom max from, thatToInclusive min toInclusive)
          case _ => that.intersect(this)
        }
      }
    override def isEmpty() = false
    override def upperBoundExclusive() = Some((toInclusive + 1).toChar)
    override def iterate() = (from to toInclusive).iterator
    override def toString() =
      s"[${formatChar(from)}, ${formatChar(toInclusive)}]"
  }

  final case object AnyChar extends SymbolicLabel {
    override def overlaps(that: SymbolicLabel) = true
    override def intersect(that: SymbolicLabel) = that
    override def isEmpty() = false
    override def subtract(that: SymbolicLabel) = ???
    override def upperBoundExclusive() = None
    override def iterate() = (Char.MinValue to Char.MaxValue).iterator
    override def toString() = "Σ"
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
) extends GraphvizDumper {

  // TODO reverse lookup and show the label origins!
  private def labelAnnotation(t: AutomataTypes.Transition) =
    t.label().toString()

  private def stateAnnotation(productState: AutomataTypes.State) = {
    val (leftState, rightState) = originOf(productState)
    s"${productState} = ${leftState}/${rightState}"
  }

  def toDot() =
    product.toDot(
      transitionAnnotator = labelAnnotation,
      stateAnnotator = stateAnnotation
    )

  def originOf(productState: AutomataTypes.State) =
    productStateToTermStates(productState)

  def originOfTransition(t: AutomataTypes.Transition) = {
    val (leftOrigin, rightOrigin) = termTransitionToProductTransitions
      .filter(_._2 contains t)
      .keys
      .toSet
      .toSeq
      .partition(_._1 == TermOrigin.Left)

    (leftOrigin(0)._2, rightOrigin(0)._2)
  }

  def resultsOf(
      leftOrRight: TermOrigin.TermOrigin
  )(transition: AutomataTypes.Transition) =
    termTransitionToProductTransitions.get((leftOrRight, transition))
}

object TermOrigin extends Enumeration {
  type TermOrigin = Value
  val Left, Right = Value
}
