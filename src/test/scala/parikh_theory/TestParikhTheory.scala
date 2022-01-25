package uuverifiers.parikh_theory

import org.scalatest.funsuite.AnyFunSuite
import ap.SimpleAPI
import SimpleAPI.ProverStatus
import ap.terfor.TerForConvenience._
import SymbolicLabelConversions._

class TestParikhTheory extends AnyFunSuite with Tracing {

  test("length constraint for trivial automaton works") {
    val aut = AutomatonBuilder()
      .addStates(List(0, 1))
      .setInitial(0)
      .setAccepting(1)
      .addTransition(0, 'a', 1)
      .getAutomaton()

    val lt = LengthCounting(IndexedSeq(aut))

    assert(TestUtilities.onlyReturnsLength(lt, 1))
  }

  //              c
  //       +--------------------------------+
  //       |                                v
  //     +---+    a       #===#     b     #===#
  // --> | 0 | ---------> H 1 H --------> H 2 H
  //     +---+            #===#           #===#
  test("3-state, 1-register loop-free automaton has correct lengths") {
    val aut = AutomatonBuilder()
      .addStates(List(0, 1, 2))
      .setInitial(0)
      .setAccepting(1, 2)
      .addTransition(0, 'c', 2)
      .addTransition(0, 'a', 1)
      .addTransition(1, 'b', 2)
      .getAutomaton()

    val lt = LengthCounting(IndexedSeq(aut))

    TestUtilities.ensuresAlways(lt) {
      case (lengths, order) =>
        implicit val o = order
        disj(lengths(0) === l(1), lengths(0) === l(2))(order)
    }
  }

  test("bug #1: 1.smt2 incorrect parikh image (minimised)") {
    val aut = AutomatonBuilder()
      .addStates(List(0, 1))
      .setAccepting(0, 1)
      .setInitial(0)
      .addTransition(0, 'a', 1)
      .addTransition(1, 'b', 1)
      .getAutomaton()

    val lt = LengthCounting(IndexedSeq(aut))

    TestUtilities.ensuresAlways(lt) {
      case (lengths, order) =>
        implicit val o = order
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
    "4-state, per-transition register automaton with loop without product has correct values"
  ) {
    val aut = AutomatonBuilder()
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
      .getAutomaton()

    TestUtilities.bothImplementationsHaveSameImage(aut)
  }

  //       +---+  a  +---+  b  +---+
  //   --> | 0 | --> | 1 | --> | 3 | -->
  //       +---+     +---+     +---+
  //                           |
  //                    b      |
  //               +-----------+
  //       +---+<--+
  //       | 2 |
  //       +---+
  test("old implementation bug for 4-state automaton") {
    import ap.terfor.conjunctions.Conjunction
    import ap.PresburgerTools

    val aut = AutomatonBuilder()
      .addStates(0 to 3)
      .setAccepting(3)
      .setInitial(0)
      .addTransition(0, 'a', 1)
      .addTransition(1, 'b', 3)
      .addTransition(3, 'b', 2)
      .getAutomaton()

    val alphabet = "ab".toCharArray

    val presburgerFormulation = new PresburgerParikhImage(aut)

    SimpleAPI.withProver { p =>
      val a = p.createConstantRaw("a")
      val b = p.createConstantRaw("b")
      val constants = Seq(a, b)

      import p._
      implicit val order = p.order

      val oldImage = presburgerFormulation.parikhImage(
        constants,
        TestUtilities
          .alphabetCounter(alphabet) _
      )

      val reduced = PresburgerTools.elimQuantifiersWithPreds(
        Conjunction.conj(oldImage, p.order)
      )

      val constraint = conj(reduced, b === 1, a === 1)

      p addAssertion constraint

      val res = p.???

      val simplifiedOld = pp(simplify(asIFormula(reduced)))

      withClue(s"${simplifiedOld}")(assert(res == ProverStatus.Sat))
    }
  }

  test("two instances of the predicate") {
    val aut = AutomatonBuilder()
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
      .getAutomaton()

    val alphabet = "abc-".toCharArray

    val theory = ParikhTheory(IndexedSeq(aut))(
      TestUtilities.alphabetCounter(alphabet) _,
      alphabet.length
    )

    SimpleAPI.withProver { p =>
      val constantsA = p.createConstantsRaw("a", 0 until theory.monoidDimension)
      val constantsB = p.createConstantsRaw("b", 0 until theory.monoidDimension)

      p addTheory theory

      implicit val o = p.order

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
    val aut = AutomatonBuilder()
      .addStates(List(0, 1))
      .setInitial(0)
      .setAccepting(1)
      .addTransition(0, 'a', 1)
      .getAutomaton()

    TestUtilities.bothImplementationsHaveSameImage(aut)
  }

  test("product parikh image removes non-common transitions") {

    def commonBits() =
      AutomatonBuilder()
        .addStates(0 to 3)
        .setAccepting(3)
        .setInitial(0)
        .addTransition(0, 'a', 1)
        .addTransition(1, 'b', 2)
        .addTransition(2, 'c', 3)

    TestUtilities.productsAreEqual(
      commonBits()
        .addTransition(3, 'b', 3)
        .addTransition(1, 'b', 3)
        .addTransition(2, 'b', 2)
        .getAutomaton(),
      commonBits()
        .addStates(Seq(4))
        .addTransition(1, 'b', 4)
        .addTransition(4, 'b', 3)
        .getAutomaton()
    )
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
    "product of 4-state, per-transition register automaton with loop has correct values"
  ) {
    def baseMaker() =
      AutomatonBuilder()
        .addStates(0 to 16)
        .setAccepting(3)
        .setInitial(0)
        .addTransition(0, 'a', 1)
        .addTransition(0, '-', 2)
        .addTransition(1, '-', 3)
        .addTransition(1, 'b', 0)
        .addTransition(2, '-', 3)
        .addTransition(2, 'c', 2)
        .addTransition(3, '-', 2)

    val leftAut = baseMaker()
      .addTransition(0, 'a', 3)
      .addTransition(3, 'a', 0)
      .addTransition(2, 'b', 13)
      .addTransition(2, 'c', 4)
      .getAutomaton()

    val rightAut = baseMaker()
      .addTransition(2, '-', 0)
      .addTransition(0, '-', 0)
      .addTransition(0, 'a', 16)
      .addTransition(2, 'b', 16)
      .addTransition(3, 'e', 16)
      .addTransition(4, 'd', 16)
      .setAccepting(0, 1, 2, 3)
      .getAutomaton()

    TestUtilities.productsAreEqual(leftAut, rightAut)

  }

  test("regression: path not in image appears") {
    def baseMaker() =
      AutomatonBuilder()
        .addStates(0 to 3)
        .setAccepting(3)
        .setInitial(0)
        .addTransition(0, 'e', 1)
        .addTransition(0, 'e', 2)
        .addTransition(1, 'a', 1)
        .addTransition(1, 'b', 3)
        .addTransition(2, 'd', 3)
        .addTransition(2, 'c', 2)

    val leftAut = baseMaker()
      .addStates(Seq(4))
      .setAccepting(4)
      .addTransition(0, 'a', 4)
      .getAutomaton()

    val rightAut = baseMaker()
      .getAutomaton()

    val alphabet = "abcde".toCharArray

    val theory = ParikhTheory(IndexedSeq(leftAut, rightAut))(
      TestUtilities.alphabetCounter(alphabet) _,
      alphabet.length
    )

    SimpleAPI.withProver { p =>
      val constants = alphabet.map(c => p.createConstantRaw(c.toString)).toSeq
      val vars = alphabet.zip(constants).toMap

      p addTheory theory

      implicit val o = p.order

      p addAssertion (theory allowsMonoidValues constants)
      p scope {
        p addAssertion (vars('c') === 2)
        p addAssertion (vars('e') === 0)

        val res = p.???
        withClue(s": ${p.partialModel}")(assert(res == ProverStatus.Unsat))
      }

      p scope {
        p addAssertion (vars('d') === vars('b'))
        val res = p.???
        withClue(s": ${p.partialModel}")(assert(res == ProverStatus.Unsat))
      }

      p scope {
        p addAssertion (vars('a') === vars('c'))
        val res = p.???
        withClue(s": ${p.partialModel}")(assert(res == ProverStatus.Sat))

        p scope {
          p addAssertion (vars('a') =/= 0)
          val res = p.???
          withClue(s": ${p.partialModel}")(assert(res == ProverStatus.Unsat))
        }
      }

    }

  }

  test("minimal product broken") {
    def baseMaker() =
      AutomatonBuilder()
        .addStates(0 to 1)
        .setAccepting(1)
        .setInitial(0)
        .addTransition(0, 'a', 1)

    val leftAut = baseMaker().getAutomaton()
    val rightAut = baseMaker().getAutomaton()

    val alphabet = "a".toCharArray

    val theory = ParikhTheory(IndexedSeq(leftAut, rightAut))(
      TestUtilities.alphabetCounter(alphabet) _,
      alphabet.length
    )

    SimpleAPI.withProver { p =>
      val constants = alphabet.map(c => p.createConstantRaw(c.toString)).toSeq
      val a = constants(0)

      p addTheory theory

      implicit val o = p.order

      p addAssertion (theory allowsMonoidValues constants)
      p addAssertion (a =/= 1)

      val res = p.???
      withClue(s": ${p}")(assert(res == ProverStatus.Unsat))

    }

  }

  test("ostrich bug reconstruction #1") {
    import SymbolicLabel.{CharRange, SingleChar}

    val leftAut =
      AutomatonBuilder()
        .addStates(0 to 1)
        .setAccepting(1)
        .setInitial(0)
        .addTransition(0, SingleChar('c'), 1)
        .getAutomaton()

    val rightAut = AutomatonBuilder()
      .addStates(0 to 2)
      .setAccepting(0, 1)
      .setInitial(2)
      .addTransition(0, SingleChar('c'), 1)
      .addTransition(1, CharRange(0, 'x'), 0)
      .addTransition(1, SingleChar('y'), 2)
      .addTransition(1, CharRange('z', Char.MaxValue), 0)
      .addTransition(2, CharRange(0, 'w'), 0)
      .addTransition(2, SingleChar('x'), 1)
      .addTransition(2, CharRange('y', Char.MaxValue), 0)
      .getAutomaton()

    val theory = LengthCounting(IndexedSeq(leftAut, rightAut))

    SimpleAPI.withProver { p =>
      val length = p.createConstantRaw("length")

      p addTheory theory

      implicit val o = p.order

      p addAssertion (theory allowsMonoidValues IndexedSeq(length))
      p addAssertion length > 1
      val res = p.???

      withClue("")(assert(res == ProverStatus.Unsat))

    }
  }

  test("ostrich bug#2 reconstruction") {
    import SymbolicLabel.CharRange

    val leftAut = AutomatonBuilder()
      .addStates(0 to 2)
      .setAccepting(2)
      .setInitial(0)
      .addTransition(0, CharRange(0, 'g'), 0)
      .addTransition(0, 'h', 1)
      .addTransition(1, 'i', 2)
      .addTransition(2, CharRange(0, Char.MaxValue), 2)
      .getAutomaton()

    val rightAut = Regex("ahia").toAutomaton()

    val theory = LengthCounting(IndexedSeq(leftAut, rightAut))

    SimpleAPI.withProver { p =>
      val length = p.createConstantRaw("length")
      p addTheory theory
      implicit val o = p.order

      p addAssertion (theory allowsMonoidValues IndexedSeq(length))
      p addAssertion (length > 1)
      val res = p.???

      withClue(s": ${p}")(assert(res == ProverStatus.Sat))

    }

  }

  test("Register automaton with two orthogonal registers works") {
    import SymbolicLabel.SingleChar

    val leftAut = AutomatonBuilder()
      .addStates(Seq(0, 1))
      .setAccepting(1)
      .setInitial(0)
      .addTransition(0, 'a', 1)
      .getAutomaton()

    val rightAut = AutomatonBuilder()
      .addStates(Seq(2, 3))
      .setAccepting(3)
      .setInitial(2)
      .addTransition(2, 'a', 3)
      .getAutomaton()

    val counters = Seq("x", "y")
    val counterToIncrement =
      Map[AutomataTypes.Transition, Map[String, Int]](
        (0, SingleChar('a'), 1) -> Map("x" -> 1),
        (2, SingleChar('a'), 3) -> Map("y" -> 1)
      )

    val theory = new RegisterCounting(
      counters,
      IndexedSeq(leftAut, rightAut),
      counterToIncrement
    )

    SimpleAPI.withProver { p =>
      val constants = counters.map(p.createConstantRaw(_)).toIndexedSeq
      p addTheory theory
      implicit val o = p.order

      p addAssertion (theory allowsMonoidValues constants)
      val res = p.???

      withClue(s": ${p}")(assert(res == ProverStatus.Sat))

    }
  }

  test("Generated length regression") {
    val a = Regex("").toAutomaton()
    val lt = LengthCounting(IndexedSeq(a))

    TestUtilities.onlyReturnsLength(lt, 0)
  }

  test(
    "peterc-pyex-doc-cav17-zz/experiments/8-600-1-7200/packages/httplib2/httplib2-cache-control/7b3cd462dc3df6b4ebfe7d49caccce971b746e012985547d646f8062.smt2/parikh-constraints-4.par crash, minimised"
  ) {
    import SymbolicLabel.CharRange

    val counters = List(
      "all_2_0",
      "aut_len_cnt_7",
      "aut_len_cnt_8"
    )

    val increments: Map[AutomataTypes.Transition, Map[String, Int]] =
      Map(
        (8, CharRange(0, 60), 8) -> Map("all_2_0" -> 1),
        (9, CharRange(0, 43), 9) -> Map("aut_len_cnt_7" -> 1),
        (11, CharRange(0, 65535), 11) -> Map("aut_len_cnt_8" -> 1)
      )

    val theories = List(
      new RegisterCounting(
        counters,
        Seq(
          AutomatonBuilder()
            .addStates(List(8))
            .setInitial(8)
            .setAccepting(8)
            .addTransition(8, CharRange(0, 60), 8)
            .getAutomaton(),
          AutomatonBuilder()
            .addStates(List(9))
            .setInitial(9)
            .setAccepting(9)
            .addTransition(9, CharRange(0, 43), 9)
            .getAutomaton(),
          AutomatonBuilder()
            .addStates(List(10, 11))
            .setInitial(10)
            .setAccepting(11)
            .addTransition(11, CharRange(0, 65535), 11)
            .getAutomaton()
        ),
        increments
      )
    )

    SimpleAPI.withProver { p =>
      // Needs to happen first because it may affect order?
      theories.foreach(p addTheory _)

      val counterToSolverConstant = counters
        .map(c => (c, p.createConstantRaw(c)))
        .toMap

      implicit val o = p.order

      for (theory <- theories) {
        val isInImage = theory allowsMonoidValues counters.map(
          counterToSolverConstant(_)
        )
        p.addAssertion(isInImage)
      }

      val satStatus = p.checkSat(true)
      println(satStatus.toString.toLowerCase())

    }
  }

}
