package uuverifiers.catra

import ap.SimpleAPI
import ap.terfor.ConstantTerm
import ap.terfor.conjunctions.{Conjunction, ReduceWithConjunction}
import uuverifiers.common.Tracing

import scala.util.{Failure, Success, Try}
import SimpleAPI.ProverStatus
import ap.parser.IFormula

import scala.collection.mutable.ArrayBuffer

import scala.annotation.tailrec

/**
 * A helper to construct backends that perform some kind of setup on the
 * Princess theorem prover and then calls the standard check-SAT features.
 */
trait PrincessBasedBackend extends Backend with Tracing {

  val arguments: CommandLineOptions

  // TODO maybe expose this as an option?
  private val RESTART_TO_FACTOR = 500L

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

  // hack to collect all formulas sent to the prover
  val formulasInSolver = new ArrayBuffer[Conjunction]

  @tailrec
  private def luby(i: Int): Int = {
    if ((i & (i + 1)) == 0) {
      (i + 1) / 2
    } else {
      var x = 1
      while (i > 2 * x - 1) x = x * 2
      luby(i - x + 1)
    }
  }

  private def checkSat(p: SimpleAPI): ProverStatus.Value =
    if (arguments.enableRestarts && arguments.backend == ChooseLazy)
      checkSatWithRestarts(p)
    else
      p.checkSat(block = true)

  @tailrec
  private def checkSatWithRestarts(
      p: SimpleAPI,
      iteration: Int = 1
  ): ProverStatus.Value = {
    val timeout: Long = luby(iteration) * RESTART_TO_FACTOR
    ap.util.Timeout.check
    p.checkSat(block = false)

    p.getStatus(timeout) match {
      case ProverStatus.Running =>
        p.stop(block = true)
        checkSatWithRestarts(p, iteration = iteration + 1)
      case r => r
    }
  }

  private def checkSolutions(p: SimpleAPI, instance: Instance)(
      counterToSolverConstant: Map[Counter, ConstantTerm]
  ): SatisfactionResult = {
    trace("final sat status")(checkSat(p)) match {
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
      arguments.withProver { p =>
        try {
          val counterToConstants = prepareSolver(p, instance)
          checkSolutions(p, instance)(counterToConstants)
        } catch {
          case _: OutOfMemoryError =>
            p.stop
            OutOfMemory
        }
      }
    }
}
