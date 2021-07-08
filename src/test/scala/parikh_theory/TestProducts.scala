package uuverifiers.parikh_theory

import org.scalatest.funsuite.AnyFunSuite
import SymbolicLabelConversions._
import AutomataTypes._
import RegexImplicits._

// TODO properties to test:
// product with self is identity
// product with empty automaton is empty
// A &&& B == B &&& A

class TestProducts extends AnyFunSuite with Tracing {

  private def prodOriginStates(prod: AnnotatedProduct) =
    prod.product.states.map(prod.originOf).unzip

  private def selectState(origin: Origin)(tpl: (State, State)) =
    if (origin == TermOrigin.Left) tpl._1 else tpl._2

  private def productContainsAutomata(
      prod: AnnotatedProduct
  )(term: Automaton, origin: Origin): Boolean = {

    val stateToProductStates =
      prod.productStateToTermStates
        .groupBy(kv => selectState(origin)(kv._2))
        .view
        .mapValues(_.keys.toSeq)

    term.transitions.forall {
      case (from, label, to) =>
        val statesExist = (stateToProductStates contains from) &&
          (stateToProductStates contains to)

        val outgoingTransitions = stateToProductStates(from)
          .flatMap(prod.product.outgoingTransitions)
          .toSet
        val possibleTargetStates = stateToProductStates(to)

        val transitionExists = possibleTargetStates.exists(
          targetProductState =>
            outgoingTransitions.contains((targetProductState, label))
        )
        statesExist && transitionExists
    }
  }

  test("trivial product") {
    val left = AutomatonBuilder()
      .addStates(List(0, 1, 2))
      .setInitial(0)
      .setAccepting(1, 2)
      .addTransition(0, 'c', 2)
      .addTransition(0, 'a', 1)
      .addTransition(1, 'b', 2)
      .getAutomaton()

    val right = AutomatonBuilder()
      .addStates(List(0, 1, 2))
      .setInitial(0)
      .setAccepting(1, 2)
      .addTransition(0, 'c', 2)
      .addTransition(0, 'a', 1)
      .addTransition(1, 'b', 2)
      .getAutomaton()

    val prod = left.productWithSources(right)
    assert(prodOriginStates(prod)._1.toSet == left.states.toSet)
    val isInProduct = productContainsAutomata(prod) _

    assert(isInProduct(left, TermOrigin.Left))
    assert(isInProduct(right, TermOrigin.Right))

  }

  test("empty product is empty") {
    val left = AutomatonBuilder()
      .addStates(List(0, 1, 2))
      .setInitial(0)
      .setAccepting(1, 2)
      .addTransition(0, 'c', 2)
      .addTransition(0, 'a', 1)
      .addTransition(1, 'b', 2)
      .getAutomaton()

    val prod = left &&& REJECT_ALL

    assert(prod.states.isEmpty)
    assert(prod == REJECT_ALL)
  }

  test("slightly more advanced product") {
    val left = AutomatonBuilder()
      .addStates(List(0, 1, 2))
      .setInitial(0)
      .setAccepting(1, 2)
      .addTransition(0, 'c', 2)
      .addTransition(0, 'a', 1)
      .addTransition(1, 'b', 2)
      .getAutomaton()

    val right = AutomatonBuilder()
      .addStates(List(0, 1, 2, 3))
      .setInitial(0)
      .setAccepting(2)
      .addTransition(0, 'z', 2)
      .addTransition(0, 'a', 1)
      .addTransition(1, 'b', 2)
      .addTransition(0, 'b', 3)
      .addTransition(3, 'a', 2)
      .getAutomaton()

    val prod = left.productWithSources(right)

    assert(
      prodOriginStates(prod)._1.toSet == left.states.toSet
    )

    val isInProduct = productContainsAutomata(prod) _

    val expectedResult = AutomatonBuilder()
      .addStates(List(0, 1, 2))
      .setInitial(0)
      .setAccepting(2)
      .addTransition(0, 'a', 1)
      .addTransition(1, 'b', 2)
      .getAutomaton()

    assert(isInProduct(expectedResult, TermOrigin.Left))
  }

  test("product with range-char label works") {
    val left = AutomatonBuilder()
      .addStates(Seq(0, 1))
      .setInitial(0)
      .setAccepting(1)
      .addTransition(0, SymbolicLabel('a', 'z'), 1)
      .getAutomaton()

    val right = AutomatonBuilder()
      .addStates(Seq(0, 1))
      .setInitial(0)
      .setAccepting(1)
      .addTransition(0, SymbolicLabel('c'), 1)
      .getAutomaton()

    val prod = left.productWithSources(right)

    assert(prod.product.transitions.toSeq == Seq((0, SymbolicLabel('c'), 1)))
    assert(prod.product.accepts("c"))
  }


  test("email and xss works") {
    val email = Regex.AnyChar.onceOrMore()
      .followedBy("@")
      .followedBy(Regex.AnyChar.onceOrMore())
      .followedBy(".")
      .followedBy(Regex.AnyChar.onceOrMore())
      .toAutomaton()

    val xss = Regex.AnyChar.onceOrMore()
      .followedBy("<script>")
      .followedBy(Regex.AnyChar.onceOrMore())
      .toAutomaton()

    val prod = email.productWithSources(xss)

    assert(!prod.product.accepts("hello"))
    assert(!prod.product.accepts("<xss>"))
    assert(!prod.product.accepts("<script>"))
    assert(prod.product.accepts("s<script>@foo.com"))
    assert(prod.product.accepts("foo@<script>.com"))
  }

}
