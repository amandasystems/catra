package uuverifiers.parikh_theory
import ap.SimpleAPI
import ap.terfor.preds.Predicate
import ap.terfor.{TermOrder, ConstantTerm}
import ap.terfor.conjunctions.{Quantifier, Conjunction}
import ap.proof.theoryPlugins.Plugin
import Plugin.AxiomSplit
import Plugin.AddAxiom
import ap.parser._
import ap.basetypes.IdealInt
import scala.util.chaining._
import scala.sys.process._
import scala.language.postfixOps
import ap.theories._
import AutomataTypes._
import SymbolicLabel.SingleChar
import IIntRelation._

object Tex {
  def smallCaps(s: String) = s"\\textsc{${s}}"
  def subscript(upper: String, lower: String) = s"${upper}_{${lower}}"
  def section(heading: String) = s"\\section{${heading}}\n"
  def environment(kind: String)(op: => String) =
    s"\\begin{${kind}}\n${op}\\end{${kind}}"
  def includeGraphics(file: String, width: String = "\\textwidth") =
    s"\\includegraphics[width=${width}]{${file}}"
  def figure(contents: String) =
    s"\\begin{figure}[h]\n\\centering\n${contents}\n\\end{figure}\n"
  def inlineMath(equation: String) = "$" + equation + "$"
  // TODO this is a stub, use the builder pattern for generating a LaTeX
  // document.
  def documentBuilder() = { object DocumentBuilder {} }
  def monospace(s: String) = { s"\\texttt{$s}" }
}

object ImageOfAutomaton  {

  import java.io._

  val texFile = new File("trace.tex")
  val texWriter = new BufferedWriter(new FileWriter(texFile))

  def predicateToTex(p: Predicate): String = p match {
    case theory.monoidMapPredicate      => Tex.smallCaps("MM")
    case theory.connectedPredicate      => Tex.smallCaps("Conn")
    case theory.transitionMaskPredicate => Tex.smallCaps("TM")
    case _                              => Tex.smallCaps(p.name)
  }

  def constantToTex(c: ConstantTerm) = {
    val lookaheadAtLeastOneNumber = """(?=\d+)"""
    val name = c.name.filterNot(_ == '_')
    name.split(lookaheadAtLeastOneNumber) match {
      case Array(letters) => letters
      case Array("all", numbers @ _*) =>
        Tex.subscript("\\alpha", numbers mkString "")
      case Array("sc", numbers @ _*) =>
        Tex.subscript("\\sigma", numbers mkString "")
      case Array(letters, numbers @ _*) =>
        Tex.subscript(letters, numbers mkString "")
    }
  }

  def timesToTex(product: ITimes) = product match {
    // -1 * -1 * x becomes -x
    case ITimes(IdealInt.MINUS_ONE, subterm) if isNegativeSingleton(subterm) =>
      s"${termToTex(subterm)}"
    // -1 * x becomes -x
    case ITimes(IdealInt.MINUS_ONE, subterm) if isSingleton(subterm) =>
      s"-${termToTex(subterm)}"
    // k * x becomes kx
    case ITimes(coefficient, subterm) if isSingleton(subterm) =>
      s"$coefficient${termToTex(subterm)}"
    // Everything else becomes k * (term)
    case ITimes(coefficient, complexTerm) =>
      s"$coefficient \\cdot (${termToTex(complexTerm)})"
  }

  def isSingleton(t: ITerm) = t match {
    case ITimes(_, _: IPlus)  => false
    case ITimes(_, _: ITimes) => false
    case _: IPlus             => false
    case _                    => true
  }

  def isNegativeSingleton(t: ITerm) = t match {
    case ITimes(IdealInt.MINUS_ONE, _: IPlus)  => false
    case ITimes(IdealInt.MINUS_ONE, _: ITimes) => false
    case ITimes(IdealInt.MINUS_ONE, _)         => true
    case _                                     => false
  }

  def plusToTex(sum: IPlus) =
    sum match {
      case IPlus(left, right: ITimes) if isNegativeSingleton(right) =>
        s"${termToTex(left)} - ${termToTex(right.subterm)}"
      case IPlus(left: ITimes, right) if isNegativeSingleton(left) =>
        s"${termToTex(right)} - ${termToTex(left.subterm)}"
      case IPlus(left, right) => s"${termToTex(left)} + ${termToTex(right)}"
    }

  def termToTex(term: ITerm): String = {
    term match {
      case sum: IPlus      => plusToTex(sum)
      case product: ITimes => timesToTex(product)
      case v: IVariable    => Tex.subscript("x", v.index.toString)
      case IIntLit(i)      => i.toString
      case IConstant(c)    => constantToTex(c)
    }
  }

  def inequalityToTex(inequality: IIntFormula) = {
    val IIntFormula(relation, term) = inequality

    import IdealInt.{ONE, ZERO, MINUS_ONE}

    val (lhs, rhs: IIntLit) = term.iterator.toSeq match {
      case Seq(l: ITerm, r: IIntLit) => (l, r.minusSimplify)
      case _                         => (term, IIntLit(ZERO))
    }

    relation match {
      case EqZero                      => s"${termToTex(lhs)} = $rhs"
      case GeqZero if rhs.value == ONE => s"${termToTex(lhs)} > 0"
      case GeqZero =>
        lhs match {
          case ITimes(MINUS_ONE, subterm) => s"${termToTex(subterm)} \\leq $rhs"
          case _ =>
            s"${termToTex(lhs)} \\geq $rhs"
        }
    }

  }

  def accumulateQuantifier(
      q: Quantifier,
      formula: IFormula,
      deBrujin: Int
  ): (IFormula, Int) = formula match {
    case ISortedQuantified(quant, _, subformula) if quant == q =>
      accumulateQuantifier(q, subformula, deBrujin + 1)
    case _ => (formula, deBrujin)
  }

  def formulaToTex(f: IFormula, debrujin: Int = 0): String = f match {
    // TODO filter boring terms
    // TODO handle sorts
    case ISortedQuantified(quant, _, subformula) => {
      val (nonQuantifiedFormula, depth) =
        accumulateQuantifier(quant, subformula, 1)
      val quantifierSymbol = quant match {
        case Quantifier.ALL => "\\forall"
        case Quantifier.EX  => "\\exists"
      }
      val subscriptPart = (0 until depth).map(i => s"x_{$i}").mkString(", ")
      s"${quantifierSymbol}_{${subscriptPart}} : ${formulaToTex(nonQuantifiedFormula, depth)}"
    }
    case IBinFormula(junctor, left, right) => {
      val fmtJunctor = junctor match {
        case IBinJunctor.And => " \\land"
        case _               => assert(false, junctor.toString)
      }
      val interestingFormulae = Seq(left, right).filter(isInteresting)
      interestingFormulae
        .map(formulaToTex(_, debrujin))
        .mkString(s"${fmtJunctor}\\\\\n&")
    }
    case inequality: IIntFormula => inequalityToTex(inequality)
    case IAtom(predicate, arguments) => {
      val argStr = arguments.map(termToTex).mkString(", ")
      s"${predicateToTex(predicate)}(${argStr})"
    }
    case IEquation(left, right) => s"${termToTex(left)} = ${termToTex(right)}"
    case IBoolLit(true)         => "\\top"
    case IBoolLit(false)        => "\\bot"
    case _ => {
      println("Missing case")
      println(f.getClass)
      println(f)
      ""
    }
  }

  def isInteresting(f: IFormula) = {
    f match {
      case IIntFormula(GeqZero, IConstant(_)) => {
        false
      }
      case _ => true
    }
  }

  def readAutomata(filename: String): IndexedSeq[Automaton] = {
    import SymbolicLabelConversions._

    // DODGE: just return a canned automaton
    IndexedSeq(
      AutomatonBuilder()
        .addStates(0 to 2)
        .setAccepting(2)
        .setInitial(0)
        .addTransition(0, 'a', 1)
        .addTransition(0, 'd', 2)
        .addTransition(1, 'b', 1)
        .addTransition(1, 'c', 2)
        .getAutomaton(),
      AutomatonBuilder()
        .addStates(0 to 2)
        .setAccepting(2)
        .setInitial(0)
        .addTransition(0, 'a', 1)
        .addTransition(0, 'c', 2)
        .addTransition(1, 'd', 1)
        .addTransition(1, 'c', 2)
        .getAutomaton()
    )
  }

  def dumpTexSnippet(tex: String) = {
    texWriter.write(tex)
    texWriter.flush()
  }

  def dumpEquation(formula: IFormula) = {
    val equation = Tex.environment("equation") {
      Tex.environment("aligned") {
        s"&${formulaToTex(formula)}"
      } + "\n"
    } + "\n"
    dumpTexSnippet(equation)
  }

  def automataFigure(dotfile: String, caption: String = "FIXME") = {
    Tex.figure(
      s"\\caption{${caption}}\n" + Tex
        .includeGraphics(dotfile.replace(".dot", ""))
    )
  }

  def actionToTex(p: SimpleAPI, order: TermOrder)(
      action: ap.proof.theoryPlugins.Plugin.Action
  ) =
    action match {
      case AxiomSplit(_, cases, _) => {
        cases.unzip._1
          .map(p.asIFormula(_))
          .map(formulaToTex(_))
          .map(Tex.inlineMath(_))
          .mkString(" $\\mid$ ")
      }
      case AddAxiom(assumptions, axiom, _) => {
        "Assumptions: \n" +
          Tex.environment("equation") {
            Tex.environment("aligned") {
              val texFormula =
                Conjunction
                  .conj(assumptions, order)
                  .pipe(p.asIFormula _)
                  .pipe(formulaToTex(_))
              s"&${texFormula}"
            } + "\n"
          } + "\n" +
          "New Axioms: " +
          p.asIFormula(axiom).pipe(formulaToTex(_)).pipe(Tex.inlineMath _)
      }
    }

  def getSymbolicParikhImage() = {
    writeFiles = false
    SimpleAPI.withProver { p =>
      p addTheory theory
      val constants = alphabet.map(c => p.createConstantRaw(c.toString())).toSeq
      implicit val o = p.order
      val isInImage = theory allowsMonoidValues constants
      val parikhImage = p.scope {
        p.addAssertion(isInImage)
        p.makeExistentialRaw(constants)

        p.setMostGeneralConstraints(true)

        println(s"Solver status: ${p.checkSat(true)}")
        // TODO: why the negation!?
        ~p.getMinimisedConstraint
      }

      println(s"Got Parikh image: ${parikhImage}")
      p addAssertion isInImage

      println(s"Status: ${p.checkSat(true)}. Partial model: ${p.partialModel}")

      p.addAssertion(~parikhImage)
      println(s"Find value outside produced image: ${p
        .checkSat(true)}. Partial model: ${p.partialModel}")
    }
    texWriter.close()
  }

  def traceASolution() = {
    writeFiles = true
    dumpTexSnippet("\\include{preamble}\n")
    dumpTexSnippet("\\begin{document}\n")

    for ((aut, i) <- automata.zipWithIndex) {
      aut.dumpDotFile(s"trace-$i.dot")
      dumpTexSnippet(
        automataFigure(
          s"trace-$i.dot",
          caption = s"Automata $i before processing."
        )
      )
    }

    SimpleAPI.withProver { p =>
      p addTheory theory
      val constants = alphabet.map(c => p.createConstantRaw(c.toString())).toSeq
      implicit val o = p.order

      for ((constant, letter) <- constants zip alphabet) {
        val monospaceLetter = Tex.monospace(letter.toString())
        val symbol = Tex.inlineMath(termToTex(constant))
        dumpTexSnippet(s"$monospaceLetter = $symbol\n")
      }

      val isInImage = theory allowsMonoidValues constants
      p.addAssertion(isInImage)

      dumpTexSnippet(Tex.section("Starting values"))
      dumpEquation(p.asIFormula(isInImage))

      println(p.checkSat(true))
    // FIXME only dump if we HAVE a model!
    // val partialSolution = p.partialModelAsFormula

    // dumpTexSnippet(Tex.section("Final assignment"))
    // dumpEquation(partialSolution)
    }
    dumpTexSnippet("\\end{document}\n")
    texWriter.close()
    "make trace.pdf" !
  }

  val automata = readAutomata("myFile.txt")
  val alphabet = automata(0).alphabet().toSeq
  var writeFiles = true

  // DODGE: we should have multiple automata
  val theory = new ParikhTheory {
    var nrInvocations = 0
    override lazy val filePrefix: String = "log"
    override val auts = automata

    override def toMonoid(t: Transition) = {
      import ap.terfor.linearcombination.LinearCombination
      import ap.basetypes.IdealInt
      val ONE = LinearCombination(IdealInt.ONE)
      val ZERO = LinearCombination(IdealInt.ZERO)

      // TODO implement this for real symbolic labels!
      val (_, SingleChar(label), _) = t: @unchecked
      alphabet.map(c => if (c == label) Some(ONE) else Some(ZERO)).toSeq

    }

    override val monoidDimension = alphabet.length

    override def actionHook(
        context: this.monoidMapPlugin.Context,
        action: String,
        actions: Seq[Plugin.Action]
    ): Unit = {
      if (!writeFiles) {
        return
      }

      dumpTexSnippet(
        Tex.section(s"Step ${nrInvocations}: Executing ${action}")
      )
      this.monoidMapPlugin.dumpGraphs(context)
      val dumpedFiles =
        this.monoidMapPlugin.dumpGraphs(context, s"trace-${nrInvocations}")
      dumpTexSnippet(
        dumpedFiles
          .map(dot => automataFigure(dot, caption = dot))
          .mkString("\n") + "\n"
      )
      SimpleAPI.withProver { p =>
        p addTheory this
        val facts = p.asIFormula(context.goal.facts)
        dumpEquation(facts)
        dumpTexSnippet(
          Tex.smallCaps(action) + ": " +
            actions
              .map(actionToTex(p, context.order))
              .mkString(", ") + "\n"
        )
      }
      nrInvocations += 1
    }

    TheoryRegistry register this
  }

  // getSymbolicParikhImage()
  traceASolution()
}
