package uuverifiers.catra
import ap.SimpleAPI
import ap.terfor.ConstantTerm
import scala.util.{Success, Try}
import uuverifiers.parikh_theory.{RegisterCounting, TracingComputation}

class PrincessBackend(override val arguments: CommandLineOptions)
    extends PrincessBasedBackend {

  override def prepareSolver(
      p: SimpleAPI,
      instance: Instance
  ): Try[Map[Counter, ConstantTerm]] = {
    import instance._
    val theories = automata.map(
      automataGroup =>
        if (arguments.trace) {
          new RegisterCounting(
            instance.counters,
            automataGroup,
            transitionToOffsets
          ) with TracingComputation
        } else {
          new RegisterCounting(
            counters,
            automataGroup,
            transitionToOffsets
          )
        }
    )

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
    Success(counterToSolverConstant)
  }

}
