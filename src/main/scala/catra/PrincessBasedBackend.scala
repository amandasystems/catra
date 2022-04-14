package uuverifiers.catra

import ap.SimpleAPI
import ap.terfor.ConstantTerm
import uuverifiers.common.Tracing
import scala.util.{Success, Failure, Try}
import SimpleAPI.ProverStatus
import ap.parser.IFormula

/**
 * A helper to construct backends that perform some kind of setup on the
 * Princess theorem prover and then calls the standard check-SAT features.
 */
trait PrincessBasedBackend extends Backend with Tracing {

  val arguments: CommandLineOptions

  import arguments._

  /**
   * Essentially performs all the logic common to both modes of operation.
   *
   * @param p A solver instance to use.
   * @param instance
   * @return A mapping from the instance's counters to their corrsponding
   * constants defined in p.
   */
  def prepareSolver(
      p: SimpleAPI,
      instance: Instance
  ): Try[Map[Counter, ConstantTerm]]

  def withProver[T](f: SimpleAPI => T): T =
    dumpSMTDir match {
      case None => SimpleAPI.withProver(f)
      case Some(dumpDir) =>
        SimpleAPI.withProver(dumpSMT = true, dumpDirectory = dumpDir)(f)
    }

  override def findImage(instance: Instance) = withProver { p =>
    val counterToSolverConstant = prepareSolver(p, instance).get
    p.makeExistentialRaw(counterToSolverConstant.values)
    p.setMostGeneralConstraints(true)
    // TODO handle responses here
    println(s"Solver status: ${p.checkSat(true)}")
    val parikhImage: IFormula = (~p.getMinimisedConstraint).notSimplify
    // TODO: translate to our representation
    println(s"Got Parikh image: ${parikhImage}")
    Success(Unsat) // FIXME: this is a mock value!
  }

  private def checkSolutions(p: SimpleAPI, instance: Instance)(
      counterToSolverConstant: Map[Counter, ConstantTerm]
  ): Try[SatisfactionResult] = {
    p.checkSat(block = false)

    // FIXME this should be handled once, in the general timeout block.
    val satStatus = timeout_ms match {
      case Some(timeout_ms) =>
        p.getStatus(timeout = timeout_ms)
      case None => p.getStatus(block = true)
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
      case ProverStatus.Running => {
        p.stop
        Success(Timeout(timeout_ms.get))
      }
      case ProverStatus.Unsat       => Success(Unsat)
      case ProverStatus.OutOfMemory => Success(OutOfMemory)
      case otherStatus =>
        Failure(
          new Exception(s"unexpected solver status: ${otherStatus}")
        )
    }
  }

  override def solveSatisfy(instance: Instance): Try[SatisfactionResult] = {
    withProver { p =>
      arguments.runWithTimeout {
        prepareSolver(p, instance).flatMap(checkSolutions(p, instance)(_))

      } match {
        case Left(someTimeout) => {
          p.stop
          Success(someTimeout)
        }
        case Right(someResult) => someResult
      }
    }
  }
}
