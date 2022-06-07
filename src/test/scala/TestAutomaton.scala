import ap.SimpleAPI
import ap.SimpleAPI.ProverStatus
import ap.terfor.TermOrder
import ap.terfor.conjunctions.Conjunction
import org.scalacheck.Properties
import org.scalatest.funsuite.AnyFunSuite
import uuverifiers.common._

class TestAutomaton extends AnyFunSuite {
  import scala.language.implicitConversions

  implicit def range2States(idxs: Range): Seq[IntState] = IntState(idxs)
  implicit def int2State(idx: Int): IntState = IntState(idx)

  test("transitions and transitionsBFS have the same transitions modulo order") {
    for (a <- AutomatonLibrary.allAutomata) {
      withClue(a) {
        assert(a.transitions.toSet == a.transitionsBreadthFirst().toSet)
      }
    }
  }

  test("Baseline Parikh image computation (empty automaton)") {
    import ap.terfor.{Formula, TerForConvenience, Term}
    import TerForConvenience._

    val aut = REJECT_ALL

    SimpleAPI.withProver { p =>
      import p._
      val c = createConstantRaw("c")
      implicit val o: TermOrder = order

      def bridgingFormula(m: Map[Transition, Term]): Formula =
        m(aut.transitions.head) === c

      p.addAssertion(aut.parikhImage(bridgingFormula _))

      assert(??? == ProverStatus.Unsat)
    }
  }

  test("Baseline Parikh image computation (trivial)") {
    import ap.terfor.{Formula, TerForConvenience, Term}
    import TerForConvenience._

    val aut = AutomatonLibrary.trivial

    SimpleAPI.withProver { p =>
      import p._
      val c = createConstantRaw("c")
      implicit val o: TermOrder = order

      def bridgingFormula(m: Map[Transition, Term]): Formula =
        m(aut.transitions.head) === c

      val pa = aut.parikhImage(bridgingFormula _)
      val img = c === 1

      addConclusion((pa & img) | (!pa & !img))

      assert(??? == ProverStatus.Valid)
    }
  }

  test("Baseline Parikh image computation (fourStatePerTransitionWithLoop)") {
    import ap.terfor.{Formula, TerForConvenience, Term}
    import TerForConvenience._

    val aut = AutomatonLibrary.fourStatePerTransitionWithLoop

    SimpleAPI.withProver { p =>
      import p._
      val a = createConstantRaw("a")
      val b = createConstantRaw("b")
      val c = createConstantRaw("c")
      implicit val o: TermOrder = order

      def bridgingFormula(m: Map[Transition, Term]): Formula =
        conj(for (t <- aut.transitions) yield t match {
          case Transition(IntState(0), _, IntState(1)) => m(t) === a
          case Transition(IntState(1), _, IntState(0)) => m(t) === b
          case Transition(IntState(2), _, IntState(2)) => m(t) === c
          case _                                       => Conjunction.TRUE
        })

      val pa = aut.parikhImage(bridgingFormula _)
      val img = (c >= 0) & (a >= 0) & (b >= 0) & (a === b | a === b + 1)

      addConclusion((pa & img) | (!pa & !img))

      assert(??? == ProverStatus.Valid)
    }
  }

  test("transitions to unreachable state disappears") {
    val unreachableTransition =
      new SymbolicTransition(IntState(2), SymbolicLabel('-'), IntState(2))
    val reachableTransition =
      new SymbolicTransition(IntState(0), SymbolicLabel('-'), IntState(1))

    val aut = AutomatonBuilder()
      .addStates(0 to 2)
      .setInitial(0)
      .setAccepting(1)
      .addTransition(reachableTransition)
      .addTransition(unreachableTransition)
      .getAutomaton()

    assert(aut.containsTransition(reachableTransition))
    assert(!aut.containsTransition(unreachableTransition))

  }

  test("transitions to dead state disappears") {
    val deadTransition =
      new SymbolicTransition(IntState(1), SymbolicLabel('-'), IntState(2))
    val reachableTransition =
      new SymbolicTransition(IntState(0), SymbolicLabel('-'), IntState(1))

    val aut = AutomatonBuilder()
      .addStates(0 to 2)
      .setInitial(0)
      .setAccepting(1)
      .addTransition(reachableTransition)
      .addTransition(deadTransition)
      .getAutomaton()

    assert(aut.containsTransition(reachableTransition))
    assert(!aut.containsTransition(deadTransition))

  }

}

object AutomatonSpecification extends Properties("Automata") {
  // TODO
}
