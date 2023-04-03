import ap.SimpleAPI
import ap.SimpleAPI.ProverStatus
import ap.terfor.TerForConvenience.*
import ap.terfor.TermOrder
import ap.terfor.equations.EquationConj
import org.scalatest.funsuite.AnyFunSuite
import uuverifiers.catra.Counter
import uuverifiers.common.SymbolicLabel.{CharRange, SingleChar}
import uuverifiers.common.SymbolicLabelConversions.*
import uuverifiers.common.*
import uuverifiers.parikh_theory.{ParikhTheory, RegisterCounting}
import scala.language.implicitConversions

class TestParikhTheory extends AnyFunSuite with Tracing {
  import scala.language.implicitConversions
  implicit def int2State(idx: Int): IntState = IntState(idx)
  implicit def range2States(idxs: Range): Seq[IntState] = IntState(idxs)

  test("length constraint for trivial automaton works") {
    val lt = LengthCounting(IndexedSeq(AutomatonLibrary.trivial))
    assert(TestUtilities.onlyReturnsLength(lt, 1))
  }

  //              c
  //       +--------------------------------+
  //       |                                v
  //     +---+    a       #===#     b     #===#
  // --> | 0 | ---------> H 1 H --------> H 2 H
  //     +---+            #===#           #===#
  test("3-state, 1-register loop-free automaton has correct lengths") {
    val lt = LengthCounting(IndexedSeq(AutomatonLibrary.threeStateLoopFree))

    TestUtilities.ensuresAlways(lt) {
      case (lengths, order) =>
        implicit val o: TermOrder = order
        disj(
          (lengths(0) === l(1)).asInstanceOf[EquationConj],
          (lengths(0) === l(2)).asInstanceOf[EquationConj]
        )(order)
    }
  }

  test("bug #1: 1.smt2 incorrect parikh image (minimised)") {
    val aut = AutomatonBuilder()
      .addStates(List(0, 1))
      .setAccepting(0, 1)
      .setInitial(0)
      .addTransition(new SymbolicTransition(0, 'a', 1))
      .addTransition(new SymbolicTransition(1, 'b', 1))
      .getAutomaton()

    val lt = LengthCounting(IndexedSeq(aut))

    TestUtilities.ensuresAlways(lt) {
      case (lengths, order) =>
        implicit val o: TermOrder = order
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
    TestUtilities.bothImplementationsHaveSameImage(
      AutomatonLibrary.fourStatePerTransitionWithLoop
    )
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
    import ap.PresburgerTools
    import ap.terfor.conjunctions.Conjunction

    val aut = AutomatonBuilder()
      .addStates(IntState(0 to 3))
      .setAccepting(3)
      .setInitial(0)
      .addTransition(new SymbolicTransition(0, 'a', 1))
      .addTransition(new SymbolicTransition(1, 'b', 3))
      .addTransition(new SymbolicTransition(3, 'b', 2))
      .getAutomaton()

    val alphabet = "ab".toCharArray

    SimpleAPI.withProver { p =>
      val a = p.createConstantRaw("a")
      val b = p.createConstantRaw("b")
      val constants = Seq(a, b)

      import p._
      implicit val order: TermOrder = p.order

      val oldImage = aut.parikhImage(
        bridgingFormula = TestUtilities.bridgingFormulaOccurrenceCounter(
          alphabet,
          alphabet.zip(constants).toMap,
          order
        )(_)
      )

      val reduced = PresburgerTools.elimQuantifiersWithPreds(
        Conjunction.conj(oldImage, p.order)
      )

      val constraint = conj(reduced, b === 1, a === 1)

      p addAssertion constraint

      val res = p.???

      val simplifiedOld = pp(simplify(asIFormula(reduced)))

      withClue(s"$simplifiedOld")(assert(res == ProverStatus.Sat))
    }
  }

  test("two instances of the predicate") {
    val aut = AutomatonBuilder()
      .addStates(0 to 3)
      .setAccepting(3)
      .setInitial(0)
      .addTransition(new SymbolicTransition(0, 'a', 1))
      .addTransition(new SymbolicTransition(0, '-', 2))
      .addTransition(new SymbolicTransition(1, '-', 3))
      .addTransition(new SymbolicTransition(1, 'b', 0))
      .addTransition(new SymbolicTransition(2, '-', 3))
      .addTransition(new SymbolicTransition(2, 'c', 2))
      .addTransition(new SymbolicTransition(3, '-', 2))
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
      .addTransition(new SymbolicTransition(0, 'a', 1))
      .getAutomaton()

    TestUtilities.bothImplementationsHaveSameImage(aut)
  }

  test("product parikh image removes non-common transitions") {

    def commonBits() =
      AutomatonBuilder()
        .addStates(0 to 3)
        .setAccepting(3)
        .setInitial(0)
        .addTransition(new SymbolicTransition(0, 'a', 1))
        .addTransition(new SymbolicTransition(1, 'b', 2))
        .addTransition(new SymbolicTransition(2, 'c', 3))

    TestUtilities.productsAreEqual(
      commonBits()
        .addTransition(new SymbolicTransition(3, 'b', 3))
        .addTransition(new SymbolicTransition(1, 'b', 3))
        .addTransition(new SymbolicTransition(2, 'b', 2))
        .getAutomaton(),
      commonBits()
        .addStates(Seq(4))
        .addTransition(new SymbolicTransition(1, 'b', 4))
        .addTransition(new SymbolicTransition(4, 'b', 3))
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
  ignore(
    "product of 4-state, per-transition register automaton with loop has correct values"
  ) {
    def baseMaker() =
      AutomatonBuilder()
        .addStates(0 to 16)
        .setAccepting(3)
        .setInitial(0)
        .addTransition(new SymbolicTransition(0, 'a', 1))
        .addTransition(new SymbolicTransition(0, '-', 2))
        .addTransition(new SymbolicTransition(1, '-', 3))
        .addTransition(new SymbolicTransition(1, 'b', 0))
        .addTransition(new SymbolicTransition(2, '-', 3))
        .addTransition(new SymbolicTransition(2, 'c', 2))
        .addTransition(new SymbolicTransition(3, '-', 2))

    val leftAut = baseMaker()
      .addTransition(new SymbolicTransition(0, 'a', 3))
      .addTransition(new SymbolicTransition(3, 'a', 0))
      .addTransition(new SymbolicTransition(2, 'b', 13))
      .addTransition(new SymbolicTransition(2, 'c', 4))
      .getAutomaton()

    val rightAut = baseMaker()
      .addTransition(new SymbolicTransition(2, '-', 0))
      .addTransition(new SymbolicTransition(0, '-', 0))
      .addTransition(new SymbolicTransition(0, 'a', 16))
      .addTransition(new SymbolicTransition(2, 'b', 16))
      .addTransition(new SymbolicTransition(3, 'e', 16))
      .addTransition(new SymbolicTransition(4, 'd', 16))
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
        .addTransition(new SymbolicTransition(0, 'e', 1))
        .addTransition(new SymbolicTransition(0, 'e', 2))
        .addTransition(new SymbolicTransition(1, 'a', 1))
        .addTransition(new SymbolicTransition(1, 'b', 3))
        .addTransition(new SymbolicTransition(2, 'd', 3))
        .addTransition(new SymbolicTransition(2, 'c', 2))

    val leftAut = baseMaker()
      .addStates(Seq(4))
      .setAccepting(4)
      .addTransition(new SymbolicTransition(0, 'a', 4))
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
        .addTransition(new SymbolicTransition(0, 'a', 1))

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
    val leftAut =
      AutomatonBuilder()
        .addStates(0 to 1)
        .setAccepting(1)
        .setInitial(0)
        .addTransition(new SymbolicTransition(0, SingleChar('c'), 1))
        .getAutomaton()

    val rightAut = AutomatonBuilder()
      .addStates(0 to 2)
      .setAccepting(0, 1)
      .setInitial(2)
      .addTransition(new SymbolicTransition(0, SingleChar('c'), 1))
      .addTransition(new SymbolicTransition(1, CharRange(0, 'x'), 0))
      .addTransition(new SymbolicTransition(1, SingleChar('y'), 2))
      .addTransition(
        new SymbolicTransition(1, CharRange('z', Char.MaxValue), 0)
      )
      .addTransition(new SymbolicTransition(2, CharRange(0, 'w'), 0))
      .addTransition(new SymbolicTransition(2, SingleChar('x'), 1))
      .addTransition(
        new SymbolicTransition(2, CharRange('y', Char.MaxValue), 0)
      )
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

    val leftAut = AutomatonBuilder()
      .addStates(0 to 2)
      .setAccepting(2)
      .setInitial(0)
      .addTransition(new SymbolicTransition(0, CharRange(0, 'g'), 0))
      .addTransition(new SymbolicTransition(0, 'h', 1))
      .addTransition(new SymbolicTransition(1, 'i', 2))
      .addTransition(new SymbolicTransition(2, CharRange(0, Char.MaxValue), 2))
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

    val leftAut = AutomatonBuilder()
      .addStates(Seq(0, 1))
      .setAccepting(1)
      .setInitial(0)
      .addTransition(Counting(0, 'a', Map(Counter("x") -> 1), 1))
      .getAutomaton()

    val rightAut = AutomatonBuilder()
      .addStates(Seq(2, 3))
      .setAccepting(3)
      .setInitial(2)
      .addTransition(Counting(2, 'a', Map(Counter("y") -> 1), 3))
      .getAutomaton()

    val counters: Set[Counter] = leftAut.counters() union rightAut.counters()

    val theory = new RegisterCounting(IndexedSeq(leftAut, rightAut))

    SimpleAPI.withProver { p =>
      val constants =
        counters.map((c: Counter) => p.createConstantRaw(c.name)).toIndexedSeq
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
    """peterc-pyex-doc-cav17-zz/experiments/8-600-1-7200/packages/httplib2/
      |httplib2-cache-control/7b3cd462dc3df6b4ebfe7d49caccce971b746e012985547d646f8062.smt2
      |/parikh-constraints-4.par crash, minimised""".stripMargin
  ) {

    val automata = Seq(
      AutomatonBuilder()
        .addStates(List(8))
        .setInitial(8)
        .setAccepting(8)
        .addTransition(
          Counting(8, CharRange(0, 60), Map(Counter("all_2_0") -> 1), 8)
        )
        .getAutomaton(),
      AutomatonBuilder()
        .addStates(List(9))
        .setInitial(9)
        .setAccepting(9)
        .addTransition(
          Counting(
            9,
            CharRange(0, 43),
            Map(Counter("aut_len_cnt_7") -> 1),
            9
          )
        )
        .getAutomaton(),
      AutomatonBuilder()
        .addStates(List(10, 11))
        .setInitial(10)
        .setAccepting(11)
        .addTransition(
          Counting(
            11,
            CharRange(0, 65535),
            Map(
              Counter("aut_len_cnt_8") -> 1
            ),
            11
          )
        )
        .getAutomaton()
    )

    val theory = new RegisterCounting(automata)

    SimpleAPI.withProver { p =>
      // Needs to happen first because it may affect order?
      p addTheory theory

      val counters = automata
        .flatMap(_.counters())
        .distinct

      val counterToSolverConstant =
        counters.map(c => c -> c.toConstant(p)).toMap

      implicit val o: TermOrder = p.order
      val isInImage = theory allowsMonoidValues counters.map(
        counterToSolverConstant(_)
      )
      p.addAssertion(isInImage)

      assert(p.checkSat(true) == SimpleAPI.ProverStatus.Unsat)
    }
  }

  test("unsat bug reproduction") {
    val c = Counter("c")

    val singleState = AutomatonBuilder()
      .addState(0)
      .setAccepting(0)
      .setInitial(0)
      .getAutomaton()

    val onlyTransition: SymbolicTransition =
      Counting(1, CharRange(1, 65535), c incrementBy 1, 2)

    val twoState = AutomatonBuilder()
      .addStates(Seq(1, 2))
      .addTransition(onlyTransition)
      .setInitial(1)
      .setAccepting(2)
      .getAutomaton()

    val theorySingle = new RegisterCounting(Seq(singleState))
    val theoryTwo = new RegisterCounting(Seq(twoState))

    SimpleAPI.withProver { p =>
      // Needs to happen first because it may affect order?
      p addTheory theorySingle
      p addTheory theoryTwo

      val cToConstant = Map(c -> c.toConstant(p))
      implicit val o: TermOrder = p.order

      p addAssertion (theorySingle allowsCounterValues cToConstant)
      p addAssertion (theoryTwo allowsCounterValues cToConstant)

      val satStatus = p.checkSat(true)
      assert(satStatus == SimpleAPI.ProverStatus.Sat)

    }
  }

  test("intersection is the empty string") {
    val c = Counter("c")

    val emptyString = AutomatonBuilder()
      .addState(0)
      .setAccepting(0)
      .setInitial(0)
      .getAutomaton()

    val onlyTransition = Counting(1, CharRange(1, 65535), c incrementBy 1, 2)

    val someOrNoChar = AutomatonBuilder()
      .addStates(Seq(1, 2))
      .addTransition(onlyTransition)
      .setInitial(1)
      .setAccepting(1)
      .setAccepting(2)
      .getAutomaton()

    val theory = new RegisterCounting(Seq(emptyString, someOrNoChar))

    SimpleAPI.withProver { p =>
      // Needs to happen first because it may affect order?
      p addTheory theory

      val cSolverVar = c.toConstant(p)
      implicit val o: TermOrder = p.order

      p addAssertion (theory allowsMonoidValues Seq(cSolverVar))

      val satStatus = p.checkSat(block = true)
      assert(satStatus == SimpleAPI.ProverStatus.Sat)

      p addAssertion (cSolverVar =/= 0)
      val res = p.???
      withClue(s"${p.partialModel}")(assert(res == ProverStatus.Unsat))
    }

  }

  test("soundness issue #2 reproduction") {
    val auts = Seq(
      AutomatonBuilder()
        .addStates(Seq(0, 1))
        .setInitial(0)
        .setAccepting(1)
        .addTransition(Counting(0, SingleChar(32), Map.empty, 1))
        .addTransition(Counting(0, CharRange(33, 65535), Map.empty, 0))
        .addTransition(Counting(1, CharRange(0, 65535), Map.empty, 1))
        .getAutomaton(),
      AutomatonBuilder()
        .addStates(Seq(2, 3, 4))
        .setInitial(2)
        .setAccepting(4)
        .addTransition(Counting(2, CharRange(85, 65535), Map.empty, 3))
        .addTransition(Counting(3, CharRange(84, 84), Map.empty, 4))
        .addTransition(Counting(4, CharRange(0, 64), Map.empty, 4))
        .addTransition(Counting(4, CharRange(0, 65535), Map.empty, 4))
        .getAutomaton(),
      AutomatonBuilder()
        .addStates(Seq(5, 6))
        .setInitial(5)
        .setAccepting(5)
        .setAccepting(6)
        .addTransition(Counting(5, CharRange(0, 65535), Map.empty, 6))
        .addTransition(Counting(6, CharRange(0, 65535), Map.empty, 6))
        .getAutomaton()
    )
    val theory = new RegisterCounting(auts)

    SimpleAPI.withProver { p =>
      p addTheory theory
      implicit val o: TermOrder = p.order
      p addAssertion (theory allowsMonoidValues Seq())
      assert(p.checkSat(block = true) == SimpleAPI.ProverStatus.Sat)

    }

  }

}
