package uuverifiers.parikh_theory

import org.scalatest.funsuite.AnyFunSuite

// TODO properties to test:
// product with self is identity
// product with empty automaton is empty
// A &&& B == B &&& A

class TestProducts extends AnyFunSuite with Tracing {

  def flattenProductStates[A <: Automaton](prod: A) = {
    prod.states
      .flatMap(_.asInstanceOf[ProductState[_]].iterator)
      .toSet
  }

  def productContainsAutomata[A1 <: Automaton, A2 <: Automaton](prod: A1)(
      term: A2
  ) = {

    val stateToProductState: Map[term.State, prod.State] = prod.states.flatMap {
      s =>
        val ps = s.asInstanceOf[ProductState[term.State]]
        ps.filter(_.isInstanceOf[term.State])
          .map(underlyingState => (underlyingState.asInstanceOf[term.State], s))
    }.toMap

    term.transitions.forall {
      case (from, label, to) =>
        (stateToProductState contains from) &&
          (stateToProductState contains to) &&
          (prod.outgoingTransitions(stateToProductState(from)) contains (
            (
              stateToProductState(
                to
              ),
              label
            )
          ))
    }
  }

  test("trivial product") {
    val left = AutomatonBuilder[Int, Char]()
      .addStates(List(0, 1, 2))
      .setInitial(0)
      .setAccepting(1, 2)
      .addTransition(0, 'c', 2)
      .addTransition(0, 'a', 1)
      .addTransition(1, 'b', 2)
      .getAutomaton()

    val right = AutomatonBuilder[Int, Char]()
      .addStates(List(0, 1, 2))
      .setInitial(0)
      .setAccepting(1, 2)
      .addTransition(0, 'c', 2)
      .addTransition(0, 'a', 1)
      .addTransition(1, 'b', 2)
      .getAutomaton()

    val prod = left &&& right

    assert(
      flattenProductStates(prod) == left.states.toSet
    )

    val isInProduct = productContainsAutomata(prod) _

    assert(isInProduct(left))
    assert(isInProduct(right))

  }

  test("empty product is empty") {
    val left = AutomatonBuilder[Int, Char]()
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
    val left = AutomatonBuilder[Int, Char]()
      .addStates(List(0, 1, 2))
      .setInitial(0)
      .setAccepting(1, 2)
      .addTransition(0, 'c', 2)
      .addTransition(0, 'a', 1)
      .addTransition(1, 'b', 2)
      .getAutomaton()

    val right = AutomatonBuilder[Int, Char]()
      .addStates(List(0, 1, 2, 3))
      .setInitial(0)
      .setAccepting(2)
      .addTransition(0, 'z', 2)
      .addTransition(0, 'a', 1)
      .addTransition(1, 'b', 2)
      .addTransition(0, 'b', 3)
      .addTransition(3, 'a', 2)
      .getAutomaton()

    val prod = left &&& right

    assert(
      flattenProductStates(prod) == left.states.toSet
    )

    val isInProduct = productContainsAutomata(prod) _

    val expectedResult = AutomatonBuilder[Int, Char]()
      .addStates(List(0, 1, 2))
      .setInitial(0)
      .setAccepting(2)
      .addTransition(0, 'a', 1)
      .addTransition(1, 'b', 2)
      .getAutomaton()

    assert(isInProduct(expectedResult))

  }

}
