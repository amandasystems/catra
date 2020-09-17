package uuverifiers.parikh_theory

import org.scalatest.funsuite.AnyFunSuite
import ap.SimpleAPI
import SimpleAPI.ProverStatus

class TestParikhTheory extends AnyFunSuite {
  test("length constraint for trivial automaton works") {

    // TODO we need a nicer way to define automata for testing!
    object Aut extends Automaton {
      type State = Int
      type Label = Int

      val initialState = 0
      def isAccept(s: Aut.State) = if (s == 1) true else false
      def outgoingTransitions(from: Aut.State) =
        if (from == 0) Iterator((1, 17)) else Iterator()
      def states = List(0, 1)
    }

    val t = new ParikhTheory(Aut)

    // TODO: this should be broken out into a function for re-use, as in
    // Ostrich+
    SimpleAPI.withProver { p =>
      import p._

      val length = createConstant("length")
      !!(length  =/= 1)

      !!((t allowsRegisterValues Seq(length)))

      val expectedStatus = ProverStatus.Unsat

      if (??? != expectedStatus) {
        assert(
          false,
          s"${???} (expected: ${expectedStatus}). Countermodel: ${partialModel}"
        )
      }
    }
  }

}
