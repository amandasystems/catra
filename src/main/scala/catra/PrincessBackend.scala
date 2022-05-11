package uuverifiers.catra
import ap.SimpleAPI
import ap.terfor.ConstantTerm
import scala.util.{Success, Try}
import uuverifiers.parikh_theory.{RegisterCounting, TracingComputation}
import uuverifiers.common.Automaton
import uuverifiers.parikh_theory.ParikhTheory
import uuverifiers.parikh_theory.Context

class PrincessBackend(override val arguments: CommandLineOptions)
    extends PrincessBasedBackend {

  override def prepareSolver(
      p: SimpleAPI,
      instance: Instance
  ): Map[Counter, ConstantTerm] = {

    import instance._

    def buildTheory(automataGroup: Seq[Automaton]) = {
      val dumpHook: Option[
        (
            uuverifiers.parikh_theory.Context,
            String,
            Seq[ap.proof.theoryPlugins.Plugin.Action]
        ) => Unit
      ] = arguments.dumpGraphvizDir.map(
        directory =>
          (context: Context, _: Any, _: Any) => context.dumpGraphs(directory)
      )

      val theory = if (arguments.trace) {
        new RegisterCounting(
          instance.counters,
          automataGroup,
          transitionToOffsets,
          dumpHook
        ) with TracingComputation
      } else {
        new RegisterCounting(
          counters,
          automataGroup,
          transitionToOffsets,
          dumpHook
        )
      }

      theory
    }

    val theories = automata.map(buildTheory _)

    // Needs to happen first because it may affect order?
    theories.foreach(p addTheory _)

    val counterToSolverConstant = counters
      .map(c => (c, p.createConstantRaw(c.name)))
      .toMap

    implicit val o = p.order

    for (constraint <- constraints) {
      p.addAssertion(
        trace("add constraint")(
          constraint toPrincess counterToSolverConstant
        )
      )
    }

    for (theory <- theories) {
      val isInImage = theory allowsMonoidValues counters.map(
        counterToSolverConstant(_)
      )
      p.addAssertion(isInImage)
    }

    counterToSolverConstant
  }

}
