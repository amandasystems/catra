package uuverifiers.common

import ap.PresburgerTools
import ap.basetypes.IdealInt
import ap.terfor.{Formula, OneTerm, TerForConvenience, Term, TermOrder}
import ap.terfor.conjunctions.Conjunction
import ap.terfor.linearcombination.LinearCombination
import uuverifiers.catra.Counter

import collection.mutable.{ArrayBuffer, HashMap, HashSet => MHashSet}
import scala.collection.mutable

object NrTransitionsOrdering extends Ordering[Automaton] {
  def compare(a: Automaton, b: Automaton): Int =
    a.transitions.lengthCompare(b.transitions)
}

/**
 An automaton as far as the Parikh Theory is concerned.
 */
trait Automaton
    extends Tracing
    with Graphable[State, SymbolicLabel]
    with GraphvizDumper {

  /**
   * Iterate over automaton states
   */
  def states: Iterable[State]

  /**
   * Given a state, iterate over all outgoing transitions
   */
  def transitionsFrom(from: State): Seq[Transition]

  // Adapt to graph notation.
  override def outgoingEdges(from: State): Seq[(State, SymbolicLabel, State)] =
    transitionsFrom(from).map {
      case Transition(from, label, to) => (from, label, to)
    }

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
      stateAnnotator = _.toPretty()
    )

  def toDot(
      transitionAnnotator: Transition => String,
      stateAnnotator: State => String
  ): String = {

    def quote(s: String) = "\"" + s + "\""

    val builder = new StringBuilder("digraph Automaton {")
    builder ++= "rankdir = LR;\n"
    builder ++= "initial [shape=plaintext,label=\"\"];\n"
    builder ++= s"initial -> ${initialState.toPretty()};\n" // Add an incoming edge to the initial state

    states.foreach { s =>
      val shape = if (isAccept(s)) "doublecircle" else "circle"
      val quotedState = quote(stateAnnotator(s))
      builder ++= s"${s.toPretty()} [shape=${shape},label=${quotedState}];\n"
      transitionsFrom(s).foreach { t =>
        val quotedLabel = quote(transitionAnnotator(t))
        builder ++= s"${t.from().toPretty()} -> ${t.to().toPretty()} [label=${quotedLabel}]\n"
      }
    }

    builder ++= "}\n"

    builder.toString()
  }

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

      for (t <- transitionsFrom(next))
        if (!disabledEdges.contains(t) &&
            (res add t.to()))
          todo = t.to() :: todo
    }

    res.toSet
  }

  /**
   * Backward-reachable states, ignoring the specified disabled edges.
   */
  def bwdReachable(disabledEdges: Set[Transition]): Set[State] = {
    val reachedFrom = new HashMap[State, ArrayBuffer[State]]

    for (t @ Transition(s1, _, s2) <- transitions)
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
      quantElim: Boolean = true
  )(implicit order: TermOrder): Conjunction = {

    import TerForConvenience._

    val stateSeq = states.toIndexedSeq
    val state2Index = stateSeq.iterator.zipWithIndex.toMap

    val initialStateInd = state2Index(initialState)

    val N = transitions.size
    val prodVars: Seq[Term] = trace("transition variables")(
      for ((_, num) <- transitions.zipWithIndex) yield v(num)
    )
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
            (for ((Transition(from, _, to), prodVar) <- transitions.iterator zip prodVars.iterator;
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
      trace("final implications")(
        (for ((finalState, finalVar) <- finalVars) yield {
          (finalVar === 0) | (zVars(finalState) === 1)
        }).toList
      )

    val prodImps =
      trace("production implications")(
        (for ((Transition(_, _, to), prodVar) <- transitions.iterator zip prodVars.iterator)
          yield ((prodVar === 0) | (zVars(state2Index(to)) > 0))).toList
      )

    // connective
    val zImps =
      trace("z-implications")((for (state <- 0 until stateSeq.size) yield {
        disjFor(
          Iterator(zVars(state) === 0) ++
            (for (t <- finalVars get state) yield (t === 1)) ++
            (for ((Transition(from, _, to), prodVar) <- transitions.iterator zip prodVars.iterator;
                  if state2Index(from) == state;
                  toInd = state2Index(to))
              yield conj(
                zVars(state) === zVars(toInd) + 1,
                geqZ(List(prodVar - 1, zVars(toInd) - 1))
              ))
        )
      }).toList)

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
      .groupBy(_.from())
      .map {
        case (state, outgoing) =>
          s"== ${fmtState(state)} ==\n" + outgoing
            .map {
              case Transition(_, label, to) =>
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

  def ++(that: Automaton): Automaton = {
    val builder = AutomatonBuilder(this)
    // FIXME this breaks for any other type of state!
    var nextFreeState =
      states.map(s => s.asInstanceOf[IntState]).max.successor()

    // No states from this are accepting anymore
    builder.setNotAccepting(states.filter(isAccept).toSeq: _*)

    states.filter(isAccept).foreach(insertCopyOfThat)

    def insertCopyOfThat(startingFrom: State) = {
      // Make fresh copies of all states, except the initial one which we merge
      // with the insertion point.
      val thatStateMap: Map[State, State] = that.states
        .map(
          s =>
            (
              s,
              if (s == that.initialState) startingFrom
              else {
                val freshState = nextFreeState
                nextFreeState = nextFreeState.successor()
                builder.addState(freshState)
                if (that isAccept s) {
                  builder setAccepting freshState
                }
                freshState
              }
            )
        )
        .toMap

      // Copy over the transitions modulo the state remapping
      that.transitions.foreach { t =>
        builder.addTransition(
          new SymbolicTransition(
            thatStateMap(t.from()),
            t.label(),
            thatStateMap(t.to())
          )
        )
      }
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

      for (tr <- transitionsFrom(next)) {
        if (!disabledEdges.contains(tr) && !reached.contains(tr.to())) {
          reached.put(tr.to(), tr :: pathSoFar)
          todo = tr.to() :: todo
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

    for (t <- transitions if keepEdge(t)) {
      builder.addTransition(t)
    }

    builder.getAutomaton()
  }

  /**
   * Iterate over all transitions.
   */
  lazy val transitions =
    (for (s1 <- states.iterator; t <- transitionsFrom(s1))
      yield t).toIndexedSeq

  override def allNodes() = states.toSeq
  override def edges() =
    transitions.map {
      case Transition(from, label, to) => (from, label, to)
    }.toSeq
  override def subgraph(selectedNodes: Set[State]): Automaton = {
    val builder = AutomatonBuilder()
    val statesToKeep = states.filter(selectedNodes.contains)
    builder.addStates(statesToKeep)
    if (selectedNodes contains initialState) {
      builder.setInitial(initialState)
      statesToKeep.filter(isAccept).foreach(builder.setAccepting(_))
    }
    builder.getAutomaton()
  }

  override def dropEdges(edgesToDrop: Set[(State, SymbolicLabel, State)]) =
    filterTransitions(t => !edgesToDrop.contains((t.from(), t.label(), t.to())))

  override def addEdges(edgesToAdd: Iterable[(State, SymbolicLabel, State)]) = {
    val builder = AutomatonBuilder(this)
    edgesToAdd.foreach {
      case (from, label, to) =>
        builder.addTransition(new SymbolicTransition(from, label, to))
    }
    builder.getAutomaton()
  }

  /**
   * Find or compute overlapping transitions based on labels. If there are no
   * overlaps, return an empty iterator. If labels overlap partially, the
   * overlap is returned.
   *
   * @param left to-label from the left automaton
   * @param right to-label from the right automaton
   * @return the computed label and corresponding to-states from the left and
   * right automaton respectively
   */
  private def transitionsWithOverlappingLabels[
      L <: Transition,
      R <: Transition
  ](
      left: Iterable[L],
      right: Iterable[R]
  ): Iterable[ProductTransition] = {
    val rightTransitions = right.toSeq

    // TODO accelerate search by sorting them by interval

    val results =
      for (leftTransition <- left; rightTransition <- rightTransitions)
        yield (leftTransition intersect rightTransition)

    results.filterNot(_.isEmpty).map(_.get)
  }

  /**
   * Compute the product of two automata.
    **/
  def productWith(that: Automaton): Automaton = {
    val productBuilder = AutomatonBuilder()
    val knownProductStates = mutable.HashSet[ProductState]()
    val statesToVisit = mutable.Queue[ProductState]()

    def newStateDiscovered(state: ProductState) =
      trace("newStateDiscovered") {
        knownProductStates += state
        statesToVisit enqueue state
        productBuilder addState state
        if ((this isAccept state.left) && (that isAccept state.right)) {
          productBuilder setAccepting trace("product accepting")(state)
        }
        state
      }

    val initial = trace("product initial state")(
      newStateDiscovered(this.initialState intersect that.initialState)
    )
    productBuilder.setInitial(initial)

    while (statesToVisit.nonEmpty) {
      ap.util.Timeout.check

      val nextTarget = statesToVisit.dequeue()
      val overlappingTransitions = trace(
        s"overlappingTransitions from $nextTarget"
      )(
        transitionsWithOverlappingLabels(
          this transitionsFrom nextTarget.left,
          that transitionsFrom nextTarget.right
        ).toSeq
      )
      overlappingTransitions.foreach { productTransition =>
        val toProductState = productTransition.to().asInstanceOf[ProductState]
        if (!(knownProductStates contains toProductState))
          newStateDiscovered(toProductState)

        if (!(productBuilder containsTransition productTransition)) {
          productBuilder.addTransition(productTransition)
        }
      }
    }
    productBuilder.getAutomaton()
  }

  /**
   * Check if a transition exists.
   *
   * @param t A transition to check for
   * @return True if t is a transition in this graph, false otherwise.
   */
  def containsTransition(t: Transition): Boolean =
    trace(s"${transitionsFrom(t.from())} contains ${t}")(
      transitionsFrom(t.from()) contains t
    )

  def counters(): Set[Counter] =
    this.transitions.flatMap(_.affectsCounters()).toSet
}

object REJECT_ALL extends Automaton {
  override val initialState = IntState(0)
  override def isAccept(_s: State) = false
  override def transitionsFrom(_from: State) = Seq()
  override def states = Seq.empty
  override lazy val isEmpty = true
  override def toString = "∅ REJECT ALL"

  override def filterTransitions(keepEdge: Transition => Boolean) = this

  override def parikhImage(
      bridgingFormula: Map[Transition, Term] => Formula,
      quantElim: Boolean = true
  )(implicit p: TermOrder): Conjunction = Conjunction.FALSE
}

///**
// * A container to store the origins of states and transitions from a product of
// * automata.
// *
// * @param product
// * @param termTransitionToProductTransitions
// * @param productStateToTermStates
// */
//sealed case class AnnotatedProduct(
//    val product: Automaton,
//    val termTransitionToProductTransitions: AutomataTypes.ProductTransitionMap,
//    val productStateToTermStates: AutomataTypes.ProductStateMap
//) extends GraphvizDumper {
//
//  // TODO reverse lookup and show the label origins!
//  private def labelAnnotation(t: Transition) =
//    t.label().toString()
//
//  private def stateAnnotation(productState: State) = {
//    val (leftState, rightState) = originOf(productState)
//    s"${productState.toPretty()} = ${leftState.toPretty()}/${rightState.toPretty()}"
//  }
//
//  def toDot() =
//    product.toDot(
//      transitionAnnotator = labelAnnotation,
//      stateAnnotator = stateAnnotation
//    )
//
//  def originOf(productState: State) =
//    productStateToTermStates(productState)
//
//  def originOfTransition(t: Transition) = {
//    val (leftOrigin, rightOrigin) = termTransitionToProductTransitions
//      .filter(_._2 contains t)
//      .keys
//      .toSet
//      .toSeq
//      .partition(_._1 == TermOrigin.Left)
//
//    (leftOrigin(0)._2, rightOrigin(0)._2)
//  }
//
//  def resultsOf(
//      leftOrRight: TermOrigin.TermOrigin
//  )(transition: Transition) =
//    termTransitionToProductTransitions.get((leftOrRight, transition))
//}
//
//object TermOrigin extends Enumeration {
//  type TermOrigin = Value
//  val Left, Right = Value
//}
