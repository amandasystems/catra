package uuverifiers.catra

import ap.SimpleAPI
import ap.terfor.ConstantTerm
import uuverifiers.common.Tracing

import scala.util.{Failure, Success, Try}
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
  ): Map[Counter, ConstantTerm]

  def withProver[T](f: SimpleAPI => T): T =
    dumpSMTDir match {
      case None => SimpleAPI.withProver(f)
      case Some(dumpDir) =>
        SimpleAPI.withProver(dumpSMT = true, dumpDirectory = dumpDir)(f)
    }

  override def findImage(instance: Instance): Try[ImageResult] = withProver {
    p =>
      val counterToSolverConstant = prepareSolver(p, instance)
      p.makeExistentialRaw(counterToSolverConstant.values)
      p.setMostGeneralConstraints(true)
      p.checkSat(block = true) match {
        case ProverStatus.Sat =>
          val parikhImage: IFormula = (~p.getMinimisedConstraint).notSimplify
          Success(new ImageResult {
            override val presburgerImage: Formula = TrueOrFalse(false) // FIXME
            override val name: String = s"non-empty image $parikhImage" // FIXME
          })
        case ProverStatus.Unsat       => Success(Unsat)
        case ProverStatus.OutOfMemory => Success(OutOfMemory)
        case otherStatus =>
          Failure(new Exception(s"unexpected solver status: $otherStatus"))
      }

  }

  private def checkSolutions(p: SimpleAPI, instance: Instance)(
      counterToSolverConstant: Map[Counter, ConstantTerm]
  ): SatisfactionResult = {
    trace("final sat status")(p.checkSat(block = true)) match {
      case ProverStatus.Sat | ProverStatus.Valid =>
        Sat(
          instance.counters
            .map(
              c => c -> p.eval(counterToSolverConstant(c)).bigIntValue
            )
            .toMap
        )
      case ProverStatus.Unsat       => Unsat
      case ProverStatus.OutOfMemory => OutOfMemory
      case otherStatus =>
        throw new Exception(s"unexpected solver status: $otherStatus")
    }
  }

  override def solveSatisfy(instance: Instance): Try[SatisfactionResult] =
    trace("solveSatisfy result") {
      withProver { p =>
        arguments.runWithTimeout(p) {
          val counterToConstants = prepareSolver(p, instance)
          checkSolutions(p, instance)(counterToConstants)
        }
      }
    }
}
