package uuverifiers.parikh_theory

import org.scalacheck.Properties
import org.scalacheck.Prop.{forAll, propBoolean}

class WordAutomaton(var word: String) extends Automaton {
  type State = Int
  type Label = Char

  val initialState = 0
  val lastState = word.length

  def isAccept(s: this.State) = s == lastState

  def outgoingTransitions(from: this.State) =
    if (from != lastState) Iterator((from + 1, word(from))) else Iterator()

  lazy val states = (0 to (word.length)).toList
}

object WordSpecification extends Properties("WordAutmata") {

  property("wordHasCorrectLength") = forAll { (word: String) =>
    val a = new WordAutomaton(word)
    val lt = LengthCounting[WordAutomaton](Array(a))

    TestUtilities.onlyReturnsLength(lt, word.length)
  }

  property("wordHasCorrectParikhImage") = forAll { (word: String) =>
    (word.length > 0) ==> {

      val a = new WordAutomaton(word)
      val alphabet = word.toSet.toSeq.sorted
      val expectedCharCounts = alphabet.map(c => word.count(_ == c))

      val pi = ParikhTheory[WordAutomaton](Array(a))(
        TestUtilities.alphabetCounter(alphabet) _,
        alphabet.length
      )

      TestUtilities.onlyReturnsCounts(pi, expectedCharCounts)
    }
  }

  // TODO the same for an entire Parikh image!
  // property("wordHasCounts") = forAll { (word: String) =>
  //   val  a = new WordAutomaton(word)
  //   val lt = ParikhTheory[Int, Char, WordAutomaton](Array(a))

  //   TestUtilities.onlyReturnsCounts(lt, word.length)
  // }
}
