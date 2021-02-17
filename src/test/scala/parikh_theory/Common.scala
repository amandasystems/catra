package uuverifiers.parikh_theory

import ap.{SimpleAPI, PresburgerTools}
import ap.terfor.{Term, Formula, TermOrder}
import ap.terfor.conjunctions.Conjunction
import SimpleAPI.ProverStatus
import org.scalatest.funsuite.AnyFunSuite
import ap.terfor.TerForConvenience._
import ap.basetypes.IdealInt

object TestUtilities extends AnyFunSuite with Tracing {

  def alphabetCounter[T](alphabet: Seq[T])(t: Any) = {
    import ap.terfor.linearcombination.LinearCombination
    import ap.basetypes.IdealInt
    val ONE = LinearCombination(IdealInt.ONE)
    val ZERO = LinearCombination(IdealInt.ZERO)

    val label = t.asInstanceOf[Tuple3[_, T, _]]._2
    alphabet.map(c => if (c == label) ONE else ZERO).toSeq
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

  def ensuresAlways(theory: ParikhTheory[_])(
      lengthConstraints: (IndexedSeq[Term], TermOrder) => Conjunction
  ) = {
    SimpleAPI.withProver { p =>
      val constants = p createConstantsRaw ("x", 0 until theory.monoidDimension)
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
    // WARNING: only works for characters (but that's all we have right now)
    val alphabet = trace("alphabet")(
      aut.transitions.map(_._2.asInstanceOf[Char]).toSet.toIndexedSeq.sorted
    )

    val pt = ParikhTheory[Automaton](Array[Automaton](aut))(
      TestUtilities.alphabetCounter(alphabet) _,
      alphabet.length
    )

    val presburgerFormulation = new PresburgerParikhImage[Automaton](aut)

    def incrementLetters(t: Any): Seq[IdealInt] = {
      import ap.basetypes.IdealInt

      val label = t.asInstanceOf[Tuple3[_, aut.Label, _]]._2
      alphabet.map(c => if (c == label) IdealInt.ONE else IdealInt.ZERO).toSeq
    }

    SimpleAPI.withProver { p =>
      val constants = p createConstantsRaw ("a", 0 until pt.monoidDimension)

      p addTheory pt
      implicit val _ = p.order
      import p._

      val newImage = pt allowsMonoidValues constants
      val oldImage = presburgerFormulation parikhImage (constants, incrementLetters _)

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

  def onlyReturnsCounts(
      theory: ParikhTheory[_],
      expectedCounts: Seq[Int]
  ) = {
    ensuresAlways(theory) {
      case (vars, order) =>
        implicit val _ = order
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
      theory: LengthCounting[_],
      length: Int
  ) = onlyReturnsCounts(theory, Seq(length))
}

class AutomatonBuilder[S, L] {
  private var _autStates = Set[S]()
  private var _transitions = Set[(S, L, S)]()
  private var _initial: Option[S] = None
  private var _accepting = Set[S]()

  def addStates(statesToAdd: Seq[S]): AutomatonBuilder[S, L] = {
    _autStates ++= statesToAdd
    this
  }

  def setInitial(newInitialState: S): AutomatonBuilder[S, L] = {
    assert(_autStates contains newInitialState)
    _initial = Some(newInitialState)
    this
  }

  def setAccepting(acceptingStates: S*): AutomatonBuilder[S, L] = {
    assert(acceptingStates forall (_autStates(_)))
    _accepting ++= acceptingStates
    this
  }

  def addTransition(from: S, label: L, to: S): AutomatonBuilder[S, L] = {
    assert((_autStates contains from) && (_autStates contains to))
    _transitions += ((from, label, to))
    this
  }

  def getAutomaton(): Automaton = {
    assert(_initial != None)

    object Aut extends Automaton {
      type State = S
      type Label = L

      override val initialState = _initial.get
      override def isAccept(s: State) = _accepting contains s
      override def outgoingTransitions(from: State) =
        _transitions
          .filter { case (thatFrom, _, _) => thatFrom == from }
          .map {
            case (_, label, to) => (to, label)
          }
          .to
      override val states = _autStates
    }

    Aut
  }
}

object AutomatonBuilder {
  def apply[S, L]() = new AutomatonBuilder[S, L]()
}
