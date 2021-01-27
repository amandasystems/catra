package uuverifiers.parikh_theory

import org.scalatest.funsuite.AnyFunSuite

class TestParikhTheory extends AnyFunSuite {
  test("length constraint for trivial automaton works") {

    // TODO we need a nicer way to define automata for testing!
    object Aut extends Automaton[Int, Int] {
      type State = Int
      type Label = Int

      val initialState = 0
      def isAccept(s: Aut.State) = if (s == 1) true else false
      def outgoingTransitions(from: Aut.State) =
        if (from == 0) Iterator((1, 17)) else Iterator()
      def states = List(0, 1)
    }

    val lt = LengthCounting[Int, Int, Aut.type](Array(Aut, Aut))

    assert(TestUtilities.onlyReturnsLength(lt, 1))
  }

}
