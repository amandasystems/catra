package uuverifiers.parikh_theory

import org.scalatest.funsuite.AnyFunSuite

class TestParikhTheory extends AnyFunSuite {

  test("length constraint for trivial automaton works") {
    val aut = AutomatonBuilder[Int, Unit]()
      .addStates(List(0, 1))
      .setInitial(0)
      .setAccepting(1)
      .addTransition(0, (), 1)
      .getAutomaton

    val lt = LengthCounting[Automaton](Array(aut))

    assert(TestUtilities.onlyReturnsLength(lt, 1))
  }

  //              c
  //       +--------------------------------+
  //       |                                v
  //     +---+    a       #===#     b     #===#
  // --> | 0 | ---------> H 1 H --------> H 2 H
  //     +---+            #===#           #===#
  test("3-state, 1-register loop-free automaton has correct lengths") {
    val aut = AutomatonBuilder[Int, Char]()
      .addStates(List(0, 1, 2))
      .setInitial(0)
      .setAccepting(1, 2)
      .addTransition(0, 'c', 2)
      .addTransition(0, 'a', 1)
      .addTransition(1, 'b', 2)
      .getAutomaton

    val lt = LengthCounting[Automaton](Array(aut))

    TestUtilities.ensuresAlways(lt) { lengths =>
      Seq(lengths(0) === 1 ||| lengths(0) === 2)
    }
  }

  test("bug #1: 1.smt2 incorrect parikh image (minimised)") {
    val aut = AutomatonBuilder[Int, Char]()
      .addStates(List(0, 1))
      .setAccepting(0, 1)
      .setInitial(0)
      .addTransition(0, 'a', 1)
      .addTransition(1, 'b', 1)
      .getAutomaton

    val lt = LengthCounting[Automaton](Array(aut))

    TestUtilities.ensuresAlways(lt)(_.map(_ >= 0))
  }

}
