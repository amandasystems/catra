package uuverifiers
import fastparse.Parsed
import uuverifiers.catra._

import java.math.BigInteger
import java.util.{Calendar, Date}
import scala.concurrent.duration.Duration
import scala.concurrent.{Await, ExecutionContext, Future, duration}
import scala.util.{Failure, Success, Try}
object Validate extends App {
  import catra.InputFileParser.assignmentAsConstraint
  import catra.SolveRegisterAutomata.measureTime

  private val config =
    catra.CommandLineOptions.parse("solve-satisfy" +: args).get
  private val validator = config.withBackend(catra.ChooseNuxmv).getBackend()

  private val instances = config.inputFiles
    .flatMap(
      f =>
        catra.InputFileParser.parseFile(f) match {
          case Parsed.Success(value, _) => Some(f -> value)
          case _                        => None
        }
    )

  private def validateUnsat(instance: Instance): Option[String] =
    validator.solveSatisfy(instance) match {
      case Success(Sat(otherAssignment)) =>
        Some(
          s"Validator disagrees with UNSAT, found result: ${assignmentAsConstraint(otherAssignment)}"
        )
      case Success(Unsat)       => None
      case Success(OutOfMemory) => Some("OOM validating Unsat!")
      case Success(Timeout(_))  => Some("Unknown: timeout validating Unsat!")
      case Failure(e)           => Some(s"Error during validation of UNSAT: $e")
    }

  private def now(): Date = Calendar.getInstance().getTime

  private def validateSat(
      assignments: Map[Counter, BigInteger],
      instance: Instance
  ): Option[String] = {

    val encodedAssignment = instance.constraints appended assignmentAsConstraint(
      assignments
    )

    val instanceWithSolutionAsserted = Instance(
      counters = instance.counters,
      automataProducts = instance.automataProducts,
      constraints = encodedAssignment
    )

    validator.solveSatisfy(instanceWithSolutionAsserted) match {
      case Success(Sat(_)) => None
      case Success(Unsat) =>
        Some(s"Validator disagrees with SAT result: $encodedAssignment")
      case Success(OutOfMemory) => Some("OOM validating SAT!")
      case Success(Timeout(_))  => Some("Unknown: timeout validating!")
      case Failure(e) =>
        Some(s"Error during validation of $encodedAssignment: $e")
    }

  }

  private def validateResult(
      instance: catra.Instance,
      value: SatisfactionResult
  ): Option[String] = value match {
    case Sat(assignments)         => validateSat(assignments, instance)
    case Unsat                    => validateUnsat(instance)
    case OutOfMemory | Timeout(_) => Some("Timeout!")
  }

  private def solveSatisfy(instance: Instance): Try[SatisfactionResult] =
    config.getBackend().solveSatisfy(instance)

  private def testInstance(instanceName: String, instance: Instance) =
    (instanceName, solveSatisfy(instance) map (validateResult(instance, _)))

  private val (foundIssue, runtime) = measureTime {
    var foundIssue = false

    implicit val ec: ExecutionContext = ExecutionContext.global

    val hardTimeout =
      config.timeout_ms
        .map(t => Duration(t * 3 + 1000, duration.MILLISECONDS))
        .getOrElse(duration.Duration.Inf)

    instances.map {
      case (name, instance) => Future { testInstance(name, instance) }
    } foreach { task =>
      val outcome = Try(Await.result(task, hardTimeout)) match {
        case Failure(exception) => s"Crash: $exception"
        case Success((instanceName, Failure(e))) =>
          Some(s"$instanceName CRASH $e")
        case Success((instanceName, Success(Some(failure)))) =>
          foundIssue = true; s"$instanceName $failure"
        case Success((instanceName, Success(None))) => s"$instanceName OK!"
      }

      println(s"${now()} $outcome")
    }
    foundIssue
  }

  println(if (foundIssue) {
    s"${now()} Validated ${instances.length} instances in ${runtime}s, with errors!"
  } else {
    s"${now()} All ${instances.length} instances validated OK in ${runtime}s!"
  })

}
