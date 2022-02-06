package uuverifiers.parikh_theory
import org.scalatest.funsuite.AnyFunSuite
import org.scalacheck.Properties
import org.scalacheck.Prop.{forAll, propBoolean}
import org.scalacheck.Gen

class TestAutomaton extends AnyFunSuite {

  test("transitions and transitionsBFS have the same transitions modulo order") {
    for (a <- AutomatonLibrary.allAutomata) {
      withClue(a) {
        assert(a.transitions.toSet == a.transitionsBreadthFirst().toSet)
      }
    }
  }
}

object AutomatonSpecification extends Properties("Automata") {
  // TODO
}
