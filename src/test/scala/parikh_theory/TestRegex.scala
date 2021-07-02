package uuverifiers.parikh_theory

import org.scalatest.funsuite.AnyFunSuite

class TestRegex extends AnyFunSuite with Tracing {

  test("empty regex") {
    val rx = Regex("")
    assert(rx == Regex.Word(""))
  }

  test("word automaton") {
    val wordAutomaton = Regex("hej").toAutomaton()
    assert(wordAutomaton accepts "hej")
    assert(!(wordAutomaton accepts "he"))
  }

  test("onceOrMore") {
    val wordAutomaton = Regex("hej").onceOrMore().toAutomaton()
    assert(wordAutomaton accepts "hej")
    assert(wordAutomaton accepts "hejhej")
    assert(!(wordAutomaton accepts ""))
    assert(!(wordAutomaton accepts "he"))
  }

}
