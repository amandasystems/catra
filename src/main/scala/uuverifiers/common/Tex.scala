package uuverifiers.common

import ap.basetypes.IdealInt
import ap.parser.IIntRelation.{EqZero, GeqZero}
import ap.parser.{
  IAtom,
  IBinFormula,
  IBinJunctor,
  IBoolLit,
  IConstant,
  IEquation,
  IFormula,
  IIntFormula,
  IIntLit,
  INot,
  IPlus,
  ISortedQuantified,
  ITerm,
  ITimes,
  IVariable
}
import ap.terfor.ConstantTerm
import ap.terfor.conjunctions.Quantifier
import ap.terfor.preds.Predicate
import uuverifiers.common

import scala.annotation.tailrec

object Tex {
  def environment(kind: String)(op: => String) =
    s"\\begin{$kind}\n$op\\end{$kind}"
  private def texMacro(name: String)(args: String*) = {
    val argFmt = args mkString "}{"
    s"\\$name{$argFmt}"
  }
  def automataFigure(dotfile: String, caption: String = "FIXME") = {
    common.Tex.figure(
      s"\\caption{${caption}}\n" + common.Tex
        .includeGraphics(dotfile.replace(".dot", ""))
    )
  }
  def inlineMath(equation: String): String = "$" + equation + "$"
  def section(heading: String): String = texMacro("section")(heading)
  def includeGraphics(file: String, width: String = "\\textwidth") =
    s"\\includegraphics[width=$width]{$file}"
  def figure(contents: String) =
    s"\\begin{figure}[h]\n\\centering\n${contents}\n\\end{figure}\n"
  def smallCaps(c: String) = texMacro("textsc")(c)
  private def predicateToTex(p: Predicate) = smallCaps(p.name)

  private def constantToTex(c: ConstantTerm) = {
    val lookaheadAtLeastOneNumber = """(?=\d+)"""
    val name = c.name.filterNot(_ == '_')
    name.split(lookaheadAtLeastOneNumber) match {
      case Array(letters) => letters
      case Array("all", numbers @ _*) =>
        subscript("\\alpha", numbers mkString "")
      case Array("sc", numbers @ _*) =>
        subscript("\\sigma", numbers mkString "")
      case Array(letters, numbers @ _*) =>
        subscript(letters, numbers mkString "")
    }
  }

  private def timesToTex(product: ITimes) = product match {
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

  private def isSingleton(t: ITerm) = t match {
    case ITimes(_, _: IPlus)  => false
    case ITimes(_, _: ITimes) => false
    case _: IPlus             => false
    case _                    => true
  }

  private def isNegativeSingleton(t: ITerm) = t match {
    case ITimes(IdealInt.MINUS_ONE, _: IPlus)  => false
    case ITimes(IdealInt.MINUS_ONE, _: ITimes) => false
    case ITimes(IdealInt.MINUS_ONE, _)         => true
    case _                                     => false
  }

  private def plusToTex(sum: IPlus) =
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
      case v: IVariable    => common.Tex.subscript("x", v.index.toString)
      case IIntLit(i)      => i.toString
      case IConstant(c)    => constantToTex(c)
    }
  }

  private def inequalityToTex(inequality: IIntFormula) = {
    val IIntFormula(relation, term) = inequality

    import IdealInt.{ONE, ZERO, MINUS_ONE}

    val (lhs, rhs: IIntLit) = (term.iterator.toSeq match {
      case Seq(l: ITerm, r: IIntLit) => (l, r.minusSimplify)
      case _                         => (term, IIntLit(ZERO))
    }): @unchecked

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

  private def isInteresting(f: IFormula) = {
    f match {
      case IIntFormula(GeqZero, IConstant(_)) => false
      case _                                  => true
    }
  }

  private def subscript(upper: String, lower: String) = s"${upper}_{$lower}"

  def formulaToTex(f: IFormula, debrujin: Int = 0): String = f match {
    // TODO filter boring terms
    // TODO handle sorts
    case ISortedQuantified(quant, _, subformula) =>
      val (nonQuantifiedFormula, depth) =
        accumulateQuantifier(quant, subformula, 1)
      val quantifierSymbol = quant match {
        case Quantifier.ALL => "\\forall"
        case Quantifier.EX  => "\\exists"
      }
      val subscriptPart = (0 until depth).map(i => s"x_{$i}").mkString(", ")
      s"${subscript(quantifierSymbol, subscriptPart)} : ${formulaToTex(nonQuantifiedFormula, depth)}"
    case IBinFormula(junctor, left, right) =>
      val fmtJunctor = junctor match {
        case IBinJunctor.And => " \\land"
        case _               => assert(false, junctor.toString)
      }
      val interestingFormulae = Seq(left, right).filter(isInteresting)
      interestingFormulae
        .map(formulaToTex(_, debrujin))
        .mkString(s" $fmtJunctor ")
    case inequality: IIntFormula => inequalityToTex(inequality)
    case IAtom(predicate, arguments) =>
      val argStr = arguments.map(termToTex).mkString(", ")
      s"${predicateToTex(predicate)}($argStr)"
    case IEquation(left, right) => s"${termToTex(left)} = ${termToTex(right)}"
    case IBoolLit(true)         => "\\top"
    case IBoolLit(false)        => "\\bot"
    case INot(subformula)       => s"\\lnot(${formulaToTex(subformula, debrujin)})"
    case _ =>
      println("Missing case")
      println(f.getClass)
      println(f)
      ""
  }

  @tailrec
  def accumulateQuantifier(
      q: Quantifier,
      formula: IFormula,
      deBrujin: Int
  ): (IFormula, Int) = formula match {
    case ISortedQuantified(quant, _, subformula) if quant == q =>
      accumulateQuantifier(q, subformula, deBrujin + 1)
    case _ => (formula, deBrujin)
  }

}
