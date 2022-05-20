import org.scalatest.funsuite.AnyFunSuite
import RegexImplicits._
import uuverifiers.common.SymbolicLabelConversions._
import uuverifiers.common._

// TODO properties to test:
// product with self is identity
// product with empty automaton is empty
// A &&& B == B &&& A

class TestProducts extends AnyFunSuite with Tracing {
  import scala.language.implicitConversions
  implicit def int2State(idx: Int): IntState = IntState(idx)
  implicit def range2States(idxs: Range): Seq[IntState] = IntState(idxs)

  private def prodOriginStates(
      prod: Automaton
  ): (Iterable[State], Iterable[State]) =
    prod.states.map { case (s: ProductState) => (s.left, s.right) }.unzip

  private def transitionsFromTerm(
      prod: Automaton,
      term: Automaton
  ): Set[Transition] = {
    prod.transitions
      .map(_.asInstanceOf[ProductTransition])
      .flatMap { pt =>
        term.transitions.filter(tt => pt isProductOf tt)
      }
      .toSet
  }

  test("trivial product") {
    val left = AutomatonBuilder()
      .addStates(List(0, 1, 2))
      .setInitial(0)
      .setAccepting(1, 2)
      .addTransition(new SymbolicTransition(0, 'c', 2))
      .addTransition(new SymbolicTransition(0, 'a', 1))
      .addTransition(new SymbolicTransition(1, 'b', 2))
      .getAutomaton()

    val right = AutomatonBuilder()
      .addStates(List(0, 1, 2))
      .setInitial(0)
      .setAccepting(1, 2)
      .addTransition(new SymbolicTransition(0, 'c', 2))
      .addTransition(new SymbolicTransition(0, 'a', 1))
      .addTransition(new SymbolicTransition(1, 'b', 2))
      .getAutomaton()

    val prod = left productWith right
    assert(prodOriginStates(prod)._1.toSet == left.states.toSet)

    assert(left.transitions.toSet == transitionsFromTerm(prod, left))
    assert(right.transitions.toSet == transitionsFromTerm(prod, right))

  }

  test("empty product is empty") {
    val left = AutomatonBuilder()
      .addStates(List(0, 1, 2))
      .setInitial(0)
      .setAccepting(1, 2)
      .addTransition(new SymbolicTransition(0, 'c', 2))
      .addTransition(new SymbolicTransition(0, 'a', 1))
      .addTransition(new SymbolicTransition(1, 'b', 2))
      .getAutomaton()

    val prod = left productWith REJECT_ALL

    assert(prod.states.isEmpty)
    assert(prod == REJECT_ALL)
  }

  test("slightly more advanced product") {

    // We need this for the literal containment to work!
    val zeroToOneOnA = new SymbolicTransition(0, 'a', 1)
    val oneToTwoOnB = new SymbolicTransition(1, 'b', 2)

    val left = AutomatonBuilder()
      .addStates(List(0, 1, 2))
      .setInitial(0)
      .setAccepting(1, 2)
      .addTransition(new SymbolicTransition(0, 'c', 2))
      .addTransition(zeroToOneOnA)
      .addTransition(oneToTwoOnB)
      .getAutomaton()

    val right = AutomatonBuilder()
      .addStates(List(0, 1, 2, 3))
      .setInitial(0)
      .setAccepting(2)
      .addTransition(new SymbolicTransition(0, 'z', 2))
      .addTransition(new SymbolicTransition(0, 'a', 1))
      .addTransition(new SymbolicTransition(1, 'b', 2))
      .addTransition(new SymbolicTransition(0, 'b', 3))
      .addTransition(new SymbolicTransition(3, 'a', 2))
      .getAutomaton()

    val prod = left productWith right

    assert(
      prodOriginStates(prod)._1.toSet == left.states.toSet
    )

    val expectedResult = AutomatonBuilder()
      .addStates(List(0, 1, 2))
      .setInitial(0)
      .setAccepting(2)
      .addTransition(zeroToOneOnA)
      .addTransition(oneToTwoOnB)
      .getAutomaton()

    assert(
      expectedResult.transitions.toSet === transitionsFromTerm(
        prod,
        expectedResult
      )
    )
  }

  test("product with range-char label works") {
    val left = AutomatonBuilder()
      .addStates(Seq(0, 1))
      .setInitial(0)
      .setAccepting(1)
      .addTransition(new SymbolicTransition(0, SymbolicLabel('a', 'z'), 1))
      .getAutomaton()

    val oneToZeroOnC =
      new SymbolicTransition(IntState(0), SymbolicLabel('c'), IntState(1))

    val right = AutomatonBuilder()
      .addStates(Seq(0, 1))
      .setInitial(0)
      .setAccepting(1)
      .addTransition(oneToZeroOnC)
      .getAutomaton()

    val prod = left productWith right

    assert(prod.accepts("c"))
    assert(prod.transitions.size == 1)
    assert(prod.transitions.head.isProductOf(oneToZeroOnC))
  }

  test("email and xss works") {
    val email = Regex.AnyChar
      .onceOrMore()
      .followedBy("@")
      .followedBy(Regex.AnyChar.onceOrMore())
      .followedBy(".")
      .followedBy(Regex.AnyChar.onceOrMore())
      .toAutomaton()

    val xss = Regex.AnyChar
      .onceOrMore()
      .followedBy("<script>")
      .followedBy(Regex.AnyChar.onceOrMore())
      .toAutomaton()

    val prod = email productWith xss

    assert(!prod.accepts("hello"))
    assert(!prod.accepts("<xss>"))
    assert(!prod.accepts("<script>"))
    assert(prod.accepts("s<script>@foo.com"))
    assert(prod.accepts("foo@<script>.com"))
  }

  test("ostrich bug#2 reconstruction") {
    val leftAut = AutomatonBuilder()
      .addStates(0 to 2)
      .setAccepting(2)
      .setInitial(0)
      .addTransition(new SymbolicTransition(0, SymbolicLabel(0, 'g'), 0))
      .addTransition(new SymbolicTransition(0, 'h', 1))
      .addTransition(new SymbolicTransition(1, 'i', 2))
      .addTransition(
        new SymbolicTransition(2, SymbolicLabel(0, Char.MaxValue), 2)
      )
      .getAutomaton()

    val rightAut = Regex("ahia").toAutomaton()
    assert(!leftAut.productWith(rightAut).isEmpty)
  }

}
