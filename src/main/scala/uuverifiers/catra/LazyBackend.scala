package uuverifiers.catra
import ap.SimpleAPI
import ap.proof.theoryPlugins.Plugin
import ap.terfor.conjunctions.{Conjunction, ReduceWithConjunction}
import ap.terfor.{ConstantTerm, TermOrder}
import uuverifiers.common.Automaton
import uuverifiers.parikh_theory.{Context, RegisterCounting, TracingComputation}

import scala.util.Try

class LazyBackend(override val arguments: CommandLineOptions)
    extends PrincessBasedBackend {

  private def traceDecision(
      context: Context,
      event: String,
      actions: Seq[Plugin.Action]
  ) = {
    System.err.println(
      s"${event}. Taking actions: ${actions.mkString(",")}"
    )
  }

  override def findImage(instance: Instance): Try[ImageResult] =
    arguments.withProver { p =>
      val counterToSolverConstant = prepareSolver(p, instance)
      ap.util.Debug.enableAllAssertions(false)

      val completeFormula = Conjunction.conj(formulasInSolver, p.order)
      //      println(completeFormula)

      val qeProver = new IterativeQuantifierElimProver(p.theories, p.order)
      val reducer = ReduceWithConjunction(Conjunction.TRUE, p.order)

      var disjuncts: List[Conjunction] = List()
      var cont = true
      while (cont) {
        ap.util.Timeout.check

        val formulaToSolve =
          reducer(Conjunction.conj(completeFormula :: disjuncts, p.order))
        val nextDisjunct = qeProver(!formulaToSolve)

        println(nextDisjunct)

        if (nextDisjunct.isTrue)
          cont = false
        else
          disjuncts = nextDisjunct :: disjuncts
      }

      if (disjuncts.isEmpty) {
        Unsat
      } else {
        val image = reducer(!Conjunction.conj(disjuncts, p.order))
        new ImageResult {
          override val presburgerImage: Formula = TrueOrFalse(false) // FIXME
          override val name: String = "non-empty image " + p.pp(
            p.asIFormula(image)
          )
        }
      }
    }

  override def prepareSolver(
      p: SimpleAPI,
      instance: Instance
  ): Map[Counter, ConstantTerm] = {

    import instance._

    p.setConstructProofs(arguments.enableClauseLearning)

    def buildTheory(automataGroup: Seq[Automaton]): RegisterCounting = {
      val dumpHook: Seq[
        (Context, String, Seq[Plugin.Action]) => Unit
      ] = arguments.dumpGraphvizDir.toSeq.map(
        directory =>
          (context: Context, event: String, _: Any) =>
            if (event == "MaterialiseProduct")
              context.dumpGraphs(directory)
      )

      val decisionTraceHook = if (arguments.printDecisions) {
        Seq(traceDecision(_, _, _))
      } else {
        Seq()
      }

      val hooks = dumpHook ++ decisionTraceHook

      val theory = if (arguments.trace) {
        new RegisterCounting(
          automataGroup,
          hooks,
          arguments.nrUnknownToMaterialiseProduct
        ) with TracingComputation
      } else {
        new RegisterCounting(
          automataGroup,
          hooks,
          arguments.nrUnknownToMaterialiseProduct
        )
      }

      theory
    }

    val theories = automataProducts.map(buildTheory _)

    // Needs to happen first because it may affect order?
    theories.foreach(p addTheory _)

    val counterToSolverConstant = counters
      .map(c => (c, p.createConstantRaw(c.name)))
      .toMap

    implicit val o: TermOrder = p.order

    for (constraint <- constraints) {
      p.addAssertion(
        trace("add constraint") {
          val f = constraint toPrincess counterToSolverConstant
          formulasInSolver += p.asConjunction(f)
          f
        }
      )
    }

    for (theory <- theories) {
      val f = theory allowsCounterValues counterToSolverConstant
      p.addAssertion(f)
      formulasInSolver += f
    }

    counterToSolverConstant
  }

}
