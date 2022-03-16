package uuverifiers.parikh_theory

import org.scalacheck.Properties
import org.scalacheck.Prop.{forAll, propBoolean}
import uuverifiers.common.Regex

object WordSpecification extends Properties("WordAutmata") {

  property("wordHasCorrectLength") = forAll { (word: String) =>
    val a = Regex(word).toAutomaton()
    val lt = LengthCounting(IndexedSeq(a))

    TestUtilities.onlyReturnsLength(lt, word.length)
  }

  property("wordHasCorrectParikhImage") = forAll { (word: String) =>
    (word.length > 0) ==> {
      val a = Regex(word).toAutomaton()
      val alphabet = word.toSet.toSeq.sorted
      val expectedCharCounts = alphabet.map(c => word.count(_ == c))
      val pi = ParikhTheory(IndexedSeq(a))(
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
