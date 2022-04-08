package uuverifiers.parikh_theory
import org.scalatest.funsuite.AnyFunSuite
import org.scalacheck.Properties
import org.scalacheck.Prop.{forAll, propBoolean}
import org.scalacheck.Gen

import ap.SimpleAPI
import ap.SimpleAPI.ProverStatus
import ap.terfor.conjunctions.Conjunction
import uuverifiers.common.AutomataTypes

class TestAutomaton extends AnyFunSuite {

  test("transitions and transitionsBFS have the same transitions modulo order") {
    for (a <- AutomatonLibrary.allAutomata) {
      withClue(a) {
        assert(a.transitions.toSet == a.transitionsBreadthFirst().toSet)
      }
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

      val pa = aut.parikhImage(bridgingFormula _, List(c))
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
          case (0, _, 1) => m(t) === a
          case (1, _, 0) => m(t) === b
          case (2, _, 2) => m(t) === c
          case _         => Conjunction.TRUE
        })

      val pa = aut.parikhImage(bridgingFormula _, List(a, b, c))
      val img = (c >= 0) & (a >= 0) & (b >= 0) & (a === b | a === b + 1)

      addConclusion((pa & img) | (!pa & !img))

      assert(??? == ProverStatus.Valid)
    }
  }
}

object AutomatonSpecification extends Properties("Automata") {
  // TODO
}
