package uuverifiers.parikh_theory

import org.scalatest.funsuite.AnyFunSuite
import ap.SimpleAPI
import SimpleAPI.ProverStatus
import ap.terfor.TerForConvenience._

class TestParikhTheory extends AnyFunSuite {

  test("length constraint for trivial automaton works") {
    val aut = AutomatonBuilder[Int, Unit]()
      .addStates(List(0, 1))
      .setInitial(0)
      .setAccepting(1)
      .addTransition(0, (), 1)
      .getAutomaton

    val lt = LengthCounting[Automaton](Array(aut))

    assert(TestUtilities.onlyReturnsLength(lt, 1))
  }

  //              c
  //       +--------------------------------+
  //       |                                v
  //     +---+    a       #===#     b     #===#
  // --> | 0 | ---------> H 1 H --------> H 2 H
  //     +---+            #===#           #===#
  test("3-state, 1-register loop-free automaton has correct lengths") {
    val aut = AutomatonBuilder[Int, Char]()
      .addStates(List(0, 1, 2))
      .setInitial(0)
      .setAccepting(1, 2)
      .addTransition(0, 'c', 2)
      .addTransition(0, 'a', 1)
      .addTransition(1, 'b', 2)
      .getAutomaton

    val lt = LengthCounting[Automaton](Array(aut))

    TestUtilities.ensuresAlways(lt) {
      case (lengths, order) =>
        implicit val _ = order
        disj(lengths(0) === l(1), lengths(0) === l(2))
    }
  }

  test("bug #1: 1.smt2 incorrect parikh image (minimised)") {
    val aut = AutomatonBuilder[Int, Char]()
      .addStates(List(0, 1))
      .setAccepting(0, 1)
      .setInitial(0)
      .addTransition(0, 'a', 1)
      .addTransition(1, 'b', 1)
      .getAutomaton

    val lt = LengthCounting[Automaton](Array(aut))

    TestUtilities.ensuresAlways(lt) {
      case (lengths, order) =>
        implicit val _ = order
        conj(geqZ(lengths.map(l(_))))
    }
  }

  //              b
  //         +---------+
  //         v         |
  //       +---+  a  +---+  #2 +---+
  //   --> | 0 | --> | 1 | --> | 3 | -->
  //       +---+     +---+     +---+
  //         |                 | ^
  //         | #1       #5     | |
  //         v     +-----------+ |
  //       +---+<--+    #4       |
  //       | 2 | ----------------+
  //       +---+
  //       |   ^
  //       +---+
  //         c
  test(
    "4-state, per-transition register automaton with loop has correct values"
  ) {
    val aut = AutomatonBuilder[Int, Char]()
      .addStates(0 to 3)
      .setAccepting(3)
      .setInitial(0)
      .addTransition(0, 'a', 1)
      .addTransition(0, '-', 2)
      .addTransition(1, '-', 3)
      .addTransition(1, 'b', 0)
      .addTransition(2, '-', 3)
      .addTransition(2, 'c', 2)
      .addTransition(3, '-', 2)
      .getAutomaton

    TestUtilities.bothImplementationsHaveSameImage(aut)
  }

  test("old implementation bug for 4-state automaton") {
    import ap.terfor.conjunctions.Conjunction
    import ap.basetypes.IdealInt
    import ap.PresburgerTools

    val aut = AutomatonBuilder[Int, Char]()
      .addStates(0 to 3)
      .setAccepting(3)
      .setInitial(0)
      .addTransition(0, 'a', 1)
      .addTransition(0, '-', 2)
      .addTransition(1, '-', 3)
      .addTransition(1, 'b', 0)
      .addTransition(2, '-', 3)
      .addTransition(2, 'c', 2)
      .addTransition(3, '-', 2)
      .getAutomaton

    val alphabet = "-abc".toCharArray

    val presburgerFormulation = new PresburgerParikhImage[Automaton](aut)

    def incrementLetters(t: Any): Seq[IdealInt] = {
      val label = t.asInstanceOf[Tuple3[_, aut.Label, _]]._2
      alphabet.map(c => if (c == label) IdealInt.ONE else IdealInt.ZERO).toSeq
    }

    SimpleAPI.withProver { p =>
      val constants = p createConstantsRaw ("a", 0 until 4)
      val dash :+ a :+ b :+ c = constants

      import p._
      implicit val order = p.order

      val oldImage = presburgerFormulation parikhImage (constants, incrementLetters _)

      val reduced = PresburgerTools.elimQuantifiersWithPreds(
        Conjunction.conj(oldImage, p.order)
      )

      p addAssertion conj(reduced, a === 1, dash === 1, b === 0, c === 0)

      val res = p.???

      val simplifiedOld = pp(simplify(asIFormula(reduced)))

      withClue(s"${simplifiedOld}")(assert(res == ProverStatus.Sat))
    }
  }

  test("two instances of the predicate") {
    val aut = AutomatonBuilder[Int, Char]()
      .addStates(0 to 3)
      .setAccepting(3)
      .setInitial(0)
      .addTransition(0, 'a', 1)
      .addTransition(0, '-', 2)
      .addTransition(1, '-', 3)
      .addTransition(1, 'b', 0)
      .addTransition(2, '-', 3)
      .addTransition(2, 'c', 2)
      .addTransition(3, '-', 2)
      .getAutomaton

    val alphabet = "abc-".toCharArray

    val theory = ParikhTheory[Automaton](Array(aut))(
      TestUtilities.alphabetCounter(alphabet) _,
      alphabet.length
    )

    SimpleAPI.withProver { p =>
      val constantsA = p createConstantsRaw ("a", 0 until theory.monoidDimension)
      val constantsB = p createConstantsRaw ("b", 0 until theory.monoidDimension)

      p addTheory theory

      implicit val _ = p.order

      val clause = disjFor(
        theory allowsMonoidValues constantsA,
        theory allowsMonoidValues constantsB
      )

      p addAssertion clause

      val res = p.???
      withClue(s"${clause}")(assert(res == ProverStatus.Sat))

    }
  }

  test("parikh image for trivial automaton works") {
    val aut = AutomatonBuilder[Int, Char]()
      .addStates(List(0, 1))
      .setInitial(0)
      .setAccepting(1)
      .addTransition(0, 'a', 1)
      .getAutomaton

    TestUtilities.bothImplementationsHaveSameImage(aut)
  }

}
