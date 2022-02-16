package uuverifiers.parikh_theory
import ap.SimpleAPI
import scala.util.{Success, Failure, Try}
import ap.terfor.ConstantTerm
import SimpleAPI.ProverStatus
import ap.parser.IFormula

class PrincessBackend(private val arguments: CommandLineOptions)
    extends Backend
    with Tracing {

  import arguments._

  /**
   * Essentially performs all the logic common to both modes of operation.
   *
   * @param p A solver instance to use.
   * @param instance
   * @return A mapping from the instance's counters to their corrsponding
   * constants defined in p.
   */
  private def prepareSolver(
      p: SimpleAPI,
      instance: Instance
  ): Map[Counter, ConstantTerm] = {
    import instance._
    val theories = automata.map(
      automataGroup =>
        if (arguments.trace) {
          new RegisterCounting(
            instance.counters,
            automataGroup,
            instance.transitionToOffsets
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
    counterToSolverConstant
  }

  def withProver[T](f: SimpleAPI => T): T =
    dumpSMTDir match {
      case None => SimpleAPI.withProver(f)
      case Some(dumpDir) =>
        SimpleAPI.withProver(dumpSMT = true, dumpDirectory = dumpDir)(f)
    }

  override def findImage(instance: Instance) = withProver { p =>
    val counterToSolverConstant = prepareSolver(p, instance)
    p.makeExistentialRaw(counterToSolverConstant.values)
    p.setMostGeneralConstraints(true)
    // TODO handle responses here
    println(s"Solver status: ${p.checkSat(true)}")
    val parikhImage: IFormula = (~p.getMinimisedConstraint).notSimplify
    // TODO: translate to our representation
    println(s"Got Parikh image: ${parikhImage}")
    Success(Unsat) // FIXME: this is a mock value!
  }

  override def solveSatisfy(instance: Instance): Try[SatisfactionResult] = {
    withProver { p =>
      val counterToSolverConstant = prepareSolver(p, instance)
      p.checkSat(block = false)
      val satStatus = timeout_ms match {
        case Some(timeout_ms) => p.getStatus(timeout = timeout_ms)
        case None             => p.getStatus(block = true)
      }

      satStatus match {
        case ProverStatus.Sat | ProverStatus.Valid => {
          Success(
            Sat(
              instance.counters
                .map(
                  c => c -> p.eval(counterToSolverConstant(c)).bigIntValue
                )
                .toMap
            )
          )
        }
        case ProverStatus.Unsat       => Success(Unsat)
        case ProverStatus.Running     => p.stop(true); Success(Timeout(timeout_ms.get))
        case ProverStatus.OutOfMemory => Success(OutOfMemory)
        case otherStatus =>
          Failure(
            new Exception(s"unexpected solver status: ${otherStatus}")
          )
      }
    }

  }

}
