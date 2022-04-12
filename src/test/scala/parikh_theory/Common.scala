package uuverifiers.parikh_theory

import ap.{SimpleAPI, PresburgerTools}
import ap.terfor.{Term, Formula, TermOrder}
import ap.terfor.conjunctions.Conjunction
import SimpleAPI.ProverStatus
import org.scalatest.funsuite.AnyFunSuite
import ap.terfor.TerForConvenience._
import uuverifiers.common.AutomataTypes._
import uuverifiers.common.{Tracing, Automaton}
import ap.terfor.ConstantTerm
import ap.basetypes.IdealInt
import IdealInt.ONE
import uuverifiers.common.EdgeWrapper._

object TestUtilities extends AnyFunSuite with Tracing {

  def bridgingFormulaOccurrenceCounter(
      alphabet: Iterable[Char],
      letterVars: Map[Char, ConstantTerm],
      order: TermOrder
  )(m: Map[Transition, Term]): Formula = {
    implicit val o = order
    conj(
      alphabet.map { ch =>
        trace(s"letter balance equation: ${ch}")(
          letterVars(ch) ===
            sum(
              m.view
                .filterKeys { t =>
                  t.label() contains ch
                }
                .values
                .map(term => (ONE, l(term)))
                .toSeq
            )
        )
      }
    )
  }

  def alphabetCounter(alphabet: Iterable[Char])(t: Transition) = {
    import ap.terfor.linearcombination.LinearCombination
    import ap.basetypes.IdealInt
    val ONE = LinearCombination(IdealInt.ONE)
    val ZERO = LinearCombination(IdealInt.ZERO)

    alphabet.map(c => if (t.label() contains c) Some(ONE) else Some(ZERO)).toSeq
  }

  private def assertConstraints(
      p: ap.SimpleAPI
  )(cs: Formula, expect: ProverStatus.Value) = {
    p addAssertion cs

    val res = p.???
    val description =
      if (res == ProverStatus.Sat) s" model: ${p.partialModel}" else ""

    withClue(s"${cs}${description}")(assert(res == expect))
  }

  def ensuresAlways(theory: ParikhTheory)(
      lengthConstraints: (IndexedSeq[Term], TermOrder) => Conjunction
  ) = {
    SimpleAPI.withProver { p =>
      val constants = p.createConstantsRaw("x", 0 until theory.monoidDimension)
      p addTheory theory // It's not smart enough to realise it needs the theory

      implicit val order = p.order // Adding constants and predicates changes order

      p addAssertion ((theory allowsMonoidValues constants))
      val constraints = lengthConstraints(constants, order)
      val asserter = assertConstraints(p) _

      p scope asserter(constraints, ProverStatus.Sat)
      p scope asserter(constraints.negate, ProverStatus.Unsat)
    }
  }

  def bothImplementationsHaveSameImage(aut: Automaton) = {
    val alphabet = aut.alphabet().toSeq

    val pt = ParikhTheory(IndexedSeq[Automaton](aut))(
      TestUtilities.alphabetCounter(alphabet) _,
      alphabet.length
    )

    SimpleAPI.withProver { p =>
      val constants = p.createConstantsRaw("a", 0 until pt.monoidDimension)

      p addTheory pt
      implicit val order = p.order
      import p._

      val newImage = pt allowsMonoidValues constants
      val oldImage = aut.parikhImage(
        bridgingFormula = bridgingFormulaOccurrenceCounter(
          alphabet,
          alphabet.zip(constants).toMap,
          order
        )(_),
        constants
      )

      val reduced = PresburgerTools.elimQuantifiersWithPreds(
        Conjunction.conj(oldImage, p.order)
      )

      p addConclusion (
        Conjunction.conj(newImage, order) ==>
          Conjunction.conj(reduced, order)
      )

      val res = p.???

      val simplifiedNew =
        pp(simplify(asIFormula(Conjunction.conj(newImage, order))))
      val simplifiedOld = pp(simplify(asIFormula(reduced)))

      withClue(s"${simplifiedOld} != ${simplifiedNew}")(
        assert(res == ProverStatus.Valid)
      )
    }

    true
  }

  def productsAreEqual(left: Automaton, right: Automaton) = {
    val leftLabels = left.transitions.map(_._2).toSet
    val rightLabels = right.transitions.map(_._2).toSet
    val alphabet = trace("alphabet")(
      (leftLabels.flatMap(_.iterate()) ++ rightLabels
        .flatMap(_.iterate())).toIndexedSeq.sorted
    )

    val pt = ParikhTheory(IndexedSeq[Automaton](left, right))(
      TestUtilities.alphabetCounter(alphabet) _,
      alphabet.length
    )

    SimpleAPI.withProver { p =>
      val constants = alphabet.map(c => p.createConstantRaw(c.toString)).toSeq

      p addTheory pt

      implicit val order = p.order
      import p._

      val oldImage = (left &&& right).parikhImage(
        bridgingFormula = bridgingFormulaOccurrenceCounter(
          alphabet,
          alphabet.zip(constants).toMap,
          order
        )(_),
        constants
      )

      val newImage = pt allowsMonoidValues constants

      val reduced = PresburgerTools.elimQuantifiersWithPreds(
        Conjunction.conj(oldImage, p.order)
      )

      p addConclusion (Conjunction.conj(newImage, order) ==>
        Conjunction.conj(reduced, order))

      val res = p.???
      val simplifiedNew =
        pp(simplify(asIFormula(Conjunction.conj(newImage, order))))
      val simplifiedOld = pp(simplify(asIFormula(reduced)))
      val model =
        if (res == ProverStatus.Invalid) p.partialModel.toString() else ""

      withClue(s"${simplifiedOld} != ${simplifiedNew} in ${model}")(
        assert(res == ProverStatus.Valid)
      )
    }
    true
  }

  def onlyReturnsCounts(
      theory: ParikhTheory,
      expectedCounts: Seq[Int]
  ) = {
    ensuresAlways(theory) {
      case (vars, order) =>
        implicit val order2 = order
        conj(
          vars
            .zip(expectedCounts)
            .map {
              case (x, expected) => x === l(expected)
            }
        )
    }

    true
  }

  def onlyReturnsLength(
      theory: ParikhTheory,
      length: Int
  ) = onlyReturnsCounts(theory, Seq(length))
}
