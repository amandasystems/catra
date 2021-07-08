package uuverifiers.parikh_theory

import org.scalatest.funsuite.AnyFunSuite
import RegexImplicits._

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
    assert(wordAutomaton accepts "hejhejhej")
    assert(!(wordAutomaton accepts ""))
    assert(!(wordAutomaton accepts "he"))
    assert(!(wordAutomaton accepts "hejh"))
  }

  test("followedBy") {
    val aut = Regex.AnyChar.followedBy("h").toAutomaton()
    assert(aut accepts "ah")
  }

  test("slightlyComplicated") {
    val email = Regex.AnyChar.onceOrMore()
      .followedBy("@")
      .followedBy(Regex.AnyChar.onceOrMore())
      .followedBy(".com")
      .toAutomaton()

    assert(email accepts "hej@bobo.com")
  }

}
