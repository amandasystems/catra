package uuverifiers.catra

import ap.SimpleAPI
import ap.SimpleAPI.ProverStatus
import ap.terfor.ConstantTerm
import ap.terfor.conjunctions.Conjunction
import uuverifiers.catra.SolveRegisterAutomata.measureTime
import uuverifiers.common.Tracing

import java.math.BigInteger
import scala.annotation.tailrec
import scala.collection.mutable.ArrayBuffer
import scala.util.Try

/**
 * A helper to construct backends that perform some kind of setup on the
 * Princess theorem prover and then calls the standard check-SAT features.
 */
trait PrincessBasedBackend extends Backend with Tracing {

  val arguments: CommandLineOptions

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

  def checkSat(p: SimpleAPI): ProverStatus.Value =
    if (arguments.enableRestarts && arguments.backend == ChooseLazy)
      checkSatWithRestarts(p)
    else
      p.checkSat(block = true)

  @tailrec
  private def checkSatWithRestarts(
      p: SimpleAPI,
      iteration: Int = 1
  ): ProverStatus.Value = {
    val timeout: Long = luby(iteration) * arguments.restartTimeoutFactor
    ap.util.Timeout.check
    p.checkSat(block = false)

    p.getStatus(timeout) match {
      case ProverStatus.Running =>
        p.stop(block = true)
        if (arguments.printDecisions) System.err.println("Restart!")
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

  private def deterministicValidator(
      arguments: CommandLineOptions
  ): LazyBackend = {
    val validatorTimeout = arguments.timeout_ms.map(_ * 2)
    val timeoutArgs = validatorTimeout
      .map(to => Seq("--timeout", to.toString))
      .getOrElse(Seq.empty)
    new LazyBackend(
      CommandLineOptions
        .parse(
          Array(
            "solve-satisfy",
            "--backend",
            "lazy",
            "--no-restarts"
          ) ++ timeoutArgs
        )
        .get
    )
  }

  private def nuxmvValidator(arguments: CommandLineOptions): NUXMVBackend = {
    val validatorTimeout = arguments.timeout_ms.map(_ * 10)
    val timeoutArgs = validatorTimeout
      .map(to => Seq("--timeout", to.toString))
      .getOrElse(Seq.empty)
    new NUXMVBackend(
      CommandLineOptions
        .parse(
          Array(
            "solve-satisfy",
            "--backend",
            "nuxmv"
          ) ++ timeoutArgs
        )
        .get
    )
  }

  private def otherBackendAgrees(
      result: SatisfactionResult,
      instance: Instance,
      validator: Backend
  ): Boolean = {
    System.err.print(
      s"[${result.name}] Validating with ${validator.getClass.toString}..."
    )
    var succeededValidation = true

    val (validationResult, runtime) = measureTime {
      result match {
        case Unsat =>
          validator.solveSatisfy(instance).get match {
            case Sat(assignments) =>
              succeededValidation = false
              "FAILED\nValidator disagrees with UNSAT, found SAT:\n" + assignments
                .mkString(",")
            case Unsat => "OK"
            case e     => s"Validation Error: $e"
          }

        case Sat(assignments) =>
          val instanceWithSolutionAsserted = Instance(
            counters = instance.counters,
            automataProducts = instance.automataProducts,
            constraints =
              instance.constraints appended assignmentAsConstraint(assignments)
          )
          validator.solveSatisfy(instanceWithSolutionAsserted).get match {
            case Sat(_) => "OK"
            case Unsat =>
              succeededValidation = false
              "FAILED\nValidator disagrees with solution!"
            case e => s"Validation Error: $e"
          }
      }
    }
    System.err.println(s"$validationResult in ${runtime.round}s")
    succeededValidation
  }

  private def assignmentAsConstraint(
      assignments: Map[Counter, BigInteger]
  ): Formula = assignments.foldLeft(TrueOrFalse(true).asInstanceOf[Formula]) {
    case (formulaSoFar, (c, v)) =>
      And(
        formulaSoFar,
        Inequality(CounterWithCoefficient(1, c), Equals, Constant(v.intValue()))
      )
  }

  override def solveSatisfy(instance: Instance): Try[SatisfactionResult] =
    trace("solveSatisfy result") {
      arguments.withProver { p =>
        try {
          val counterToConstants = prepareSolver(p, instance)
          val result = checkSolutions(p, instance)(counterToConstants)
          if (arguments.crossValidate && result.isSatOrUnsat()) {
            if (!otherBackendAgrees(
                  result,
                  instance,
                  nuxmvValidator(arguments)
                ))
              throw new Exception("nuXmv disagrees with solution!")
          }
          result
        } catch {
          case _: OutOfMemoryError =>
            p.stop
            OutOfMemory
        }
      }
    }
}
