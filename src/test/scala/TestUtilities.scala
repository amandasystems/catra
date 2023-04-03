import ap.SimpleAPI.ProverStatus
import ap.basetypes.IdealInt.ONE
import ap.terfor.TerForConvenience.{conj, l, sum}
import ap.terfor.conjunctions.Conjunction
import ap.terfor.{ConstantTerm, Formula, Term, TermOrder}
import ap.{PresburgerTools, SimpleAPI}
import org.scalatest.funsuite.AnyFunSuite
import uuverifiers.common.{
  Automaton,
  Counting,
  State,
  SymbolicTransition,
  Tracing,
  Transition
}
import uuverifiers.parikh_theory.{ParikhTheory, RegisterCounting}
import ap.terfor.TerForConvenience.*
import ap.terfor.equations.EquationConj
import uuverifiers.catra.Counter
import uuverifiers.parikh_theory.VariousHelpers.transitionsIncrementRegisters

object TestUtilities extends AnyFunSuite with Tracing {

  def bridgingFormulaOccurrenceCounter(
      alphabet: Iterable[Char],
      letterVars: Map[Char, ConstantTerm],
      order: TermOrder
  )(m: Map[Transition, Term]): Formula = {
    import scala.language.implicitConversions

    implicit val o: TermOrder = order
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
    import ap.basetypes.IdealInt
    import ap.terfor.linearcombination.LinearCombination
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
        )(_)
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
    val auts = Seq(left, right)
      .zip(Seq("L", "R"))
      .map {
        case (a, lOrR) =>
          def letterToCounter(c: Char) = Counter(s"$lOrR$c")
          new Automaton {

            override def states: Iterable[State] = a.states
            override def transitionsFrom(from: State): Seq[Counting] = {
              a.transitionsFrom(from)
                .map {
                  case t: SymbolicTransition =>
                    t.withIncrements(
                      t.label()
                        .iterate()
                        .map(letterToCounter)
                        .map(c => c -> 1)
                        .toMap
                    )
                }
            }
            override val initialState: State = a.initialState
            override def isAccept(s: State): Boolean = a.isAccept(s)
            override def counters(): Set[Counter] =
              a.alphabet().map(letterToCounter).toSet
          }
      }

    val pt = new RegisterCounting(auts)

    SimpleAPI.withProver { p =>
      val counterToTerm =
        auts
          .flatMap(_.counters())
          .toSet
          .map((c: Counter) => c -> c.toConstant(p))
          .toMap

      p addTheory pt

      implicit val order: TermOrder = p.order
      import p._

      val product = auts(0) productWith auts(1)
      val oldImage = product.parikhImage(
        bridgingFormula =
          transitionsIncrementRegisters(product, counterToTerm)(_)
      )

      val newImage = pt allowsCounterValues (counterToTerm)

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
        implicit val order2: TermOrder = order
        conj(
          vars
            .zip(expectedCounts)
            .map {
              case (x, expected) =>
                (x === l(expected)).asInstanceOf[EquationConj]
            }
        )(order)
    }

    true
  }

  def onlyReturnsLength(
      theory: ParikhTheory,
      length: Int
  ) = onlyReturnsCounts(theory, Seq(length))
}
