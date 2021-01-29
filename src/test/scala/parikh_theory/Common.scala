package uuverifiers.parikh_theory

import ap.SimpleAPI
import SimpleAPI.ProverStatus

object TestUtilities {

  def expect(
      expectedStatus: ProverStatus.Value
  )(hook: ap.SimpleAPI => Any): Boolean = {
    SimpleAPI.withProver { p =>
      import p._

      hook(p)

      if (??? != expectedStatus) {
        println(
          s"${???} (expected: ${expectedStatus}). Countermodel: ${partialModel}"
        )
        return false
      }
    }
    true
  }

  def expectCountValues(
      theory: ParikhTheory[_],
      expectedValues: Seq[Int]
  )(
      expectStatus: ProverStatus.Value
  ): Boolean = {
    // We negate equality when proving a negative
    val negateEquality = expectStatus == ProverStatus.Unsat

    expect(expectStatus) { p =>
      import p._

      val constants =
        (0 until expectedValues.length).map(i => createConstant(s"length_${i}"))
      !!((theory allowsMonoidValues constants))

      constants.zip(expectedValues).foreach {
        case (c, expected) =>
          if (negateEquality) !!(c =/= expected) else !!(c === expected)
      }
    }
  }

  def onlyReturnsCounts(
      theory: ParikhTheory[_],
      expectedCounts: Seq[Int]
  ): Boolean = {

    val prover = expectCountValues(theory, expectedCounts) _
    prover(ProverStatus.Unsat) && prover(ProverStatus.Sat)
  }

  def onlyReturnsLength(
      theory: LengthCounting[_],
      length: Int
  ): Boolean = {
    onlyReturnsCounts(theory, Seq(length))
  }
}
