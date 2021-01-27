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

  def theoryBoilerplate(
      p: ap.SimpleAPI,
      theory: ParikhTheory[_, _, _],
      dimension: Int
  ) = {
    import p._
    val constants = (0 until dimension).map(i => createConstant(s"length_${i}"))
    !!((theory allowsRegisterValues constants))
    constants
  }

  def expectCountValues(
      negateEquality: Boolean,
      expectStatus: ProverStatus.Value,
      theory: ParikhTheory[_, _, _],
      expectedValues: Seq[Int]
  ): Boolean = {
    expect(expectStatus) { p =>
      import p._
      val constants = theoryBoilerplate(p, theory, expectedValues.length)

      constants.zip(expectedValues).foreach {
        case (c, expected) =>
          if (negateEquality) !!(c =/= expected) else !!(c === expected)
      }
    }
  }

  def onlyReturnsCounts(
      theory: ParikhTheory[_, _, _],
      expectedCounts: Seq[Int]
  ): Boolean = {

    expectCountValues(
      negateEquality = true,
      ProverStatus.Unsat,
      theory,
      expectedCounts
    ) && expectCountValues(
      negateEquality = false,
      ProverStatus.Sat,
      theory,
      expectedCounts
    )
  }

  def onlyReturnsLength(
      theory: LengthCounting[_, _, _],
      length: Int
  ): Boolean = {
    onlyReturnsCounts(theory, Seq(length))
  }
}
