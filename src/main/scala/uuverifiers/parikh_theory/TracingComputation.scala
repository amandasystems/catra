package uuverifiers.parikh_theory
import ap.SimpleAPI
import ap.parser._
import ap.proof.theoryPlugins.Plugin
import ap.proof.theoryPlugins.Plugin.{
  AddAxiom,
  AxiomSplit,
  CutSplit,
  RemoveFacts,
  ScheduleTask
}
import ap.terfor.TermOrder
import ap.terfor.conjunctions.Conjunction
import uuverifiers.common
import uuverifiers.common.Tex
import uuverifiers.common.Tex.formulaToTex

import scala.util.chaining._

// TODO: theories should get a unique trace!
// TODO: this needs to happen, somehow
trait TracingComputation extends ParikhTheory {
  var nrInvocations = 0

  import java.io._

  val texFile = new File("trace.tex")
  val texWriter = new BufferedWriter(new FileWriter(texFile))

  private def automataFigure(dotfile: String, caption: String) = {
    Tex.figure(
      s"\\caption{${caption}}\n" + Tex
        .includeGraphics(dotfile.replace(".dot", ""))
    )
  }

  private def dumpTexSnippet(tex: String) = {
    texWriter.write(tex)
    texWriter.flush()
  }

  private def dumpEquation(formula: IFormula) = {
    val equation = common.Tex.environment("equation") {
      Tex.environment("aligned") {
        s"&${formulaToTex(formula)}"
      } + "\n"
    } + "\n"
    dumpTexSnippet(equation)
  }

  private def actionToTex(p: SimpleAPI, order: TermOrder)(
      action: ap.proof.theoryPlugins.Plugin.Action
  ): String =
    action match {
      case AxiomSplit(_, cases, _) =>
        cases
          .map(_._1)
          .map(p.asIFormula)
          .map(formulaToTex(_))
          .map(Tex.inlineMath)
          .mkString(" $\\mid$ ")
      case AddAxiom(assumptions, axiom, _) =>
        "Assumptions: \n" +
          common.Tex.environment("equation") {
            common.Tex.environment("aligned") {
              val texFormula =
                Conjunction
                  .conj(assumptions, order)
                  .pipe(p.asIFormula)
                  .pipe(formulaToTex(_))
              s"&$texFormula"
            } + "\n"
          } + "\n" +
          "New Axioms: " +
          p.asIFormula(axiom).pipe(formulaToTex(_)).pipe(Tex.inlineMath)
      case ScheduleTask(_: TransitionSplitter, _) =>
        "Schedule splitting: Nothing happens!"
      case CutSplit(cut, _, _) =>
        s"Cut split: ${p.asIFormula(cut).pipe(formulaToTex(_)).pipe(Tex.inlineMath)}"
      case RemoveFacts(wasRemoved) =>
        s"Remove facts: ${p.asIFormula(wasRemoved).pipe(formulaToTex(_)).pipe(Tex.inlineMath)}"
    }

  def actionHook(
      context: uuverifiers.parikh_theory.Context,
      action: String,
      actions: Seq[Plugin.Action]
  ): Unit = {
    dumpTexSnippet(Tex.section(s"Step $nrInvocations: Executing $action"))
    val dumpedFiles =
      context.dumpGraphs(new File("."), s"trace-$nrInvocations")
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

  override def actionHooks() = super.actionHooks() appended actionHook

}
