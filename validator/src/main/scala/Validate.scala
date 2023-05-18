package uuverifiers
import fastparse.Parsed
import uuverifiers.catra.{
  Counter,
  Instance,
  OutOfMemory,
  Sat,
  SatisfactionResult,
  Timeout,
  Unsat
}

import java.math.BigInteger
import java.util.{Calendar, Date}
import scala.util.{Failure, Success, Try}
import scala.collection.parallel.CollectionConverters._

object Validate extends App {
  import catra.SolveRegisterAutomata.measureTime
  import catra.InputFileParser.assignmentAsConstraint

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
    case OutOfMemory | Timeout(_) => None
  }

  private def solveSatisfy(instance: Instance): Try[SatisfactionResult] =
    config.getBackend().solveSatisfy(instance)

  private var foundIssue = false

  private val (_, runtime) = measureTime {
    val results = instances.par
      .map {
        case (instanceName, instance) =>
          solveSatisfy(instance) match {
            case Failure(e) => (instanceName, Some(s"CRASH $e"))
            case Success(value) =>
              (instanceName, validateResult(instance, value))
          }
      }

    for ((instance, rs) <- results.iterator) {
      val outcome = rs match {
        case Some(failure) => foundIssue = true; s"FAIL $failure"
        case None          => "OK"
      }
      println(s"${now()} $instance $outcome")
    }
  }

  println(if (foundIssue) {
    s"${now()} Validated ${instances.length} instances in ${runtime}s, with errors!"
  } else {
    s"${now()} All ${instances.length} instances validated OK in ${runtime}s!"
  })

}
