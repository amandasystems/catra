package uuverifiers.parikh_theory

import ap.SimpleAPI
import SimpleAPI.ProverStatus
import ap.parser.{ITerm, IFormula}
import org.scalatest.funsuite.AnyFunSuite

// TODO make a general method to just test an automaton against a set of
// constraints.

object TestUtilities extends AnyFunSuite {
  private def assertConstraints(
      p: ap.SimpleAPI
  )(cs: IFormula, expect: ProverStatus.Value) = {
    p !! cs

    val res = p.???
    withClue(s"${cs} countermodel: ${p.partialModel}") {
      assert(res == expect)
    }
  }

  def ensuresAlways(theory: ParikhTheory[_])(
      lengthConstraints: IndexedSeq[ITerm] => Seq[IFormula]
  ) = {
    SimpleAPI.withProver { p =>
      val constants =
        (0 until theory.monoidDimension)
          .map(i => p createConstant (s"length_${i}"))

      p !! ((theory allowsMonoidValues constants))

      val constraints = lengthConstraints(constants).reduce(_ &&& _)
      val asserter = assertConstraints(p) _

      p scope asserter(constraints, ProverStatus.Sat)
      p scope asserter(~constraints, ProverStatus.Unsat)
    }
  }

  def onlyReturnsCounts(
      theory: ParikhTheory[_],
      expectedCounts: Seq[Int]
  ) = {
    ensuresAlways(theory)(_.zip(expectedCounts).map {
      case (l, expected) => l === expected
    })

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
