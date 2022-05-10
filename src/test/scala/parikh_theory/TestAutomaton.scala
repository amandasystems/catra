package uuverifiers.parikh_theory
import org.scalatest.funsuite.AnyFunSuite
import org.scalacheck.Properties

import ap.SimpleAPI
import ap.SimpleAPI.ProverStatus
import ap.terfor.conjunctions.Conjunction
import uuverifiers.common.AutomataTypes
import uuverifiers.common.REJECT_ALL
import uuverifiers.common.IntState
import uuverifiers.common.AutomatonBuilder
import uuverifiers.common.SymbolicLabel

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

  test("Verma Parikh image computation (empty automaton)") {
    import ap.terfor.{TerForConvenience, Term, Formula}
    import TerForConvenience._

    val aut = REJECT_ALL

    SimpleAPI.withProver { p =>
      import p._
      val c = createConstantRaw("c")
      implicit val o = order

      def bridgingFormula(m: Map[AutomataTypes.Transition, Term]): Formula =
        m(aut.transitions.head) === c

      p.addAssertion(aut.parikhImage(bridgingFormula _))

      assert(??? == ProverStatus.Unsat)
    }
  }

  test("Verma Parikh image computation (trivial)") {
    import ap.terfor.{TerForConvenience, Term, Formula}
    import TerForConvenience._

    val aut = AutomatonLibrary.trivial

    SimpleAPI.withProver { p =>
      import p._
      val c = createConstantRaw("c")
      implicit val o = order

      def bridgingFormula(m: Map[AutomataTypes.Transition, Term]): Formula =
        m(aut.transitions.head) === c

      val pa = aut.parikhImage(bridgingFormula _)
      val img = c === 1

      addConclusion((pa & img) | (!pa & !img))

      assert(??? == ProverStatus.Valid)
    }
  }

  test("Verma Parikh image computation (fourStatePerTransitionWithLoop)") {
    import ap.terfor.{TerForConvenience, Term, Formula}
    import TerForConvenience._

    val aut = AutomatonLibrary.fourStatePerTransitionWithLoop

    SimpleAPI.withProver { p =>
      import p._
      val a = createConstantRaw("a")
      val b = createConstantRaw("b")
      val c = createConstantRaw("c")
      implicit val o = order

      def bridgingFormula(m: Map[AutomataTypes.Transition, Term]): Formula =
        conj(for (t <- aut.transitions) yield t match {
          case (IntState(0), _, IntState(1)) => m(t) === a
          case (IntState(1), _, IntState(0)) => m(t) === b
          case (IntState(2), _, IntState(2)) => m(t) === c
          case _                             => Conjunction.TRUE
        })

      val pa = aut.parikhImage(bridgingFormula _)
      val img = (c >= 0) & (a >= 0) & (b >= 0) & (a === b | a === b + 1)

      addConclusion((pa & img) | (!pa & !img))

      assert(??? == ProverStatus.Valid)
    }
  }

  test("transitions to unreachable state disappears") {
    val unreachableTransition = (IntState(2), SymbolicLabel('-'), IntState(2))
    val reachableTransition =
      (IntState(0), SymbolicLabel('-'), IntState(1))

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
    val deadTransition = (IntState(1), SymbolicLabel('-'), IntState(2))
    val reachableTransition =
      (IntState(0), SymbolicLabel('-'), IntState(1))

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
