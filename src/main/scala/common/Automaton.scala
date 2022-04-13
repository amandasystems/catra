package uuverifiers.common

import ap.PresburgerTools
import ap.basetypes.IdealInt
import ap.terfor.{
  ConstantTerm,
  Formula,
  Term,
  TerForConvenience,
  TermOrder,
  OneTerm
}
import ap.terfor.conjunctions.Conjunction
import ap.terfor.linearcombination.LinearCombination
import collection.mutable.{HashMap, ArrayBuffer, Queue, HashSet => MHashSet}
import scala.language.implicitConversions
import EdgeWrapper._
import uuverifiers.common.Tracing

object AutomataTypes {
  type State = IntState
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

sealed case class IntState(id: Int) extends Ordered[IntState] {
  def compare(that: IntState) = this.id compare that.id
  def successor(): IntState = IntState(id + 1)
}

object IntState {
  def apply(range: Range): IndexedSeq[IntState] = range.map(IntState(_))
  def apply(ids: Int*): Seq[IntState] = ids.map(IntState(_))
  //def unapply(thisState: IntState): Some[Int] = Some(thisState.id)
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
  /**
   * Iterate over all *reachable* transitions in breadh-first order.
   *
   * @return
   */
  def transitionsBreadthFirst() =
    this.startBFSFrom(initialState).flatMap(transitionsFrom)

  def fmtState(s: State): String = {
    val initialDecoration = if (s == initialState) "➡" else ""
    val acceptingAnnotation = if (isAccept(s)) s"🏆(${s})" else s"(${s})"
    s"${initialDecoration}${acceptingAnnotation}"
  }

  /**
   * Forward-reachable states, ignoring the specified disabled edges.
   */
  def fwdReachable(disabledEdges: Set[Transition]): Set[State] = {
    var todo = List(initialState)
    val res = new MHashSet[State]

    res += initialState

    while (!todo.isEmpty) {
      val next = todo.head
      todo = todo.tail

      for ((target, l) <- outgoingTransitions(next))
        if (!disabledEdges.contains((next, l, target)) &&
            (res add target))
          todo = target :: todo
    }

    res.toSet
  }

  /**
   * Backward-reachable states, ignoring the specified disabled edges.
   */
  def bwdReachable(disabledEdges: Set[Transition]): Set[State] = {
    val reachedFrom = new HashMap[State, ArrayBuffer[State]]

    for (t @ (s1, _, s2) <- transitions)
      if (!disabledEdges.contains(t))
        reachedFrom.getOrElseUpdate(s2, new ArrayBuffer) += s1

    val res = new MHashSet[State]
    var todo = List[State]()

    for (s <- states)
      if (isAccept(s)) {
        res += s
        todo = s :: todo
      }

    while (!todo.isEmpty) {
      val next = todo.head
      todo = todo.tail

      for (sources <- reachedFrom get next)
        for (source <- sources)
          if (res add source)
            todo = source :: todo
    }

    res.toSet
  }

  /**
   * Compute an (existentially quantified) closed-form description of
   * the Parikh image. The bridging formula defines a mapping from the
   * Parikh image vectors to some feature of interest; e.g., length.
   */
  def parikhImage(
      bridgingFormula: Map[Transition, Term] => Formula,
      bridgingConstants: Seq[ConstantTerm],
      quantElim: Boolean = true
  ): Conjunction = {

    import TerForConvenience._
    implicit val order = TermOrder.EMPTY.extend(bridgingConstants)

    val stateSeq = states.toIndexedSeq
    val state2Index = stateSeq.iterator.zipWithIndex.toMap

    val initialStateInd = state2Index(initialState)

    val N = transitions.size
    val prodVars: Seq[Term] =
      for ((_, num) <- transitions.zipWithIndex) yield v(num)
    val zVars = trace("state variables")(
      for ((_, num) <- stateSeq.zipWithIndex) yield v(num + N)
    )
    val M = N + zVars.size
    val finalVars =
      (for ((state, num) <- (stateSeq filter (isAccept _)).zipWithIndex)
        yield (state2Index(state) -> v(num + M))).toMap

    val bFormula =
      trace("bridging formula")(
        bridgingFormula((transitions zip prodVars).toMap)
      )

    val finalStateFor =
      (finalVars.values.toSeq >= 0) &
        (sum(for ((_, t) <- finalVars.iterator) yield (IdealInt.ONE, l(t))) === 1)

    // equations relating the production counters
    val prodEqs =
      (for (state <- 0 until stateSeq.size) yield {
        LinearCombination(
          (for (t <- finalVars get state) yield (IdealInt.ONE, t)) ++
            (if (state == initialStateInd)
               Iterator((IdealInt.MINUS_ONE, OneTerm))
             else
               Iterator.empty) ++
            (for (((from, _, to), prodVar) <- transitions.iterator zip prodVars.iterator;
                  mult = (if (state2Index(from) == state) 1 else 0) -
                    (if (state2Index(to) == state) 1 else 0))
              yield (IdealInt(mult), prodVar)),
          order
        )
      }).toList

    val allEqs = trace("allEqs")(eqZ(prodEqs))

    val prodNonNeg =
      prodVars >= 0

    val finalImps =
      (for ((finalState, finalVar) <- finalVars) yield {
        (finalVar === 0) | (zVars(finalState) === 1)
      }).toList

    val prodImps =
      (for (((_, _, to), prodVar) <- transitions.iterator zip prodVars.iterator)
        yield ((prodVar === 0) | (zVars(state2Index(to)) > 0))).toList

    // connective
    val zImps =
      (for (state <- 0 until stateSeq.size) yield {
        disjFor(
          Iterator(zVars(state) === 0) ++
            (for (t <- finalVars get state) yield (t === 1)) ++
            (for (((from, _, to), prodVar) <- transitions.iterator zip prodVars.iterator;
                  if state2Index(from) == state;
                  toInd = state2Index(to))
              yield conj(
                zVars(state) === zVars(toInd) + 1,
                geqZ(List(prodVar - 1, zVars(toInd) - 1))
              ))
        )
      }).toList

    val matrix =
      conj(
        finalStateFor :: allEqs :: prodNonNeg :: bFormula ::
          zImps ::: prodImps ::: finalImps
      )

    val rawConstraint =
      trace("rawConstraint")(
        exists(prodVars.size + zVars.size + finalVars.size, matrix)
      )

    if (quantElim)
      trace("QE version")(
        PresburgerTools.elimQuantifiersWithPreds(rawConstraint)
      )
    else
      rawConstraint
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
   * Some accepting path of the automaton, or None if no such path
   * exists.
   */
  def acceptingPath(disabledEdges: Set[Transition]): Option[Seq[Transition]] = {
    var todo = List(initialState)
    val reached = new HashMap[State, List[Transition]]

    reached.put(initialState, List())

    while (!todo.isEmpty) {
      val next = todo.head
      todo = todo.tail
      val pathSoFar = reached(next)

      if (isAccept(next))
        return Some(pathSoFar.reverse)

      for ((target, l) <- outgoingTransitions(next)) {
        val tr = (next, l, target)
        if (!disabledEdges.contains(tr) && !reached.contains(target)) {
          reached.put(target, tr :: pathSoFar)
          todo = target :: todo
        }
      }
    }

    None
  }

  /**
   * Filter an automaton, producing a new automaton with a subset of its
   * previous edges, as defined by a predicate.
   */
  def filterTransitions(
      keepEdge: Transition => Boolean
  ): Automaton = trace("filterTransitions") {
    val builder = AutomatonBuilder()
      .addStates(trace("adding States")(states))
      .setInitial(initialState)
      .setAccepting(states.filter(isAccept).toSeq: _*)

    transitions.filter(keepEdge).foreach(builder.addTransition)

    builder.getAutomaton()
  }

  /**
   * Iterate over all transitions.
   */
  lazy val transitions =
    (for (s1 <- states.iterator; (s2, lbl) <- outgoingTransitions(s1))
      yield (s1, lbl, s2)).toIndexedSeq

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
    edgesToAdd.foreach(builder.addTransition)
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

          val productTransition = trace("productTransition")(
            (fromProductState, newLabel, toProductState)
          )

          if (!(productBuilder containsTransition productTransition)) {
            productBuilder.addTransition(
              productTransition
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
          } else {
            trace("saw transition twice!")(productTransition)
          }
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
    val newState =
      if (!_autStates.isEmpty) _autStates.max.successor() else IntState(0)
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

  def addTransition(from: State, label: Label, to: State): AutomatonBuilder = {
    assert((_autStates contains from) && (_autStates contains to))
    _transitions += ((from, label, to))
    this
  }

  def addTransition(t: (State, Label, State)): AutomatonBuilder =
    (this.addTransition(_: State, _: Label, _: State)).tupled(t)

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
    aut.transitions.foreach(builder.addTransition)
    builder
  }
}

object REJECT_ALL extends Automaton {
  override val initialState = IntState(0)
  override def isAccept(_s: AutomataTypes.State) = false
  override def outgoingTransitions(_from: AutomataTypes.State) = Iterator.empty
  override def states = Seq.empty
  override lazy val isEmpty = true
  override def toString = "∅ REJECT ALL"

  override def parikhImage(
      bridgingFormula: Map[AutomataTypes.Transition, Term] => Formula,
      bridgingConstants: Seq[ConstantTerm],
      quantElim: Boolean = true
  ): Conjunction = Conjunction.FALSE
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
