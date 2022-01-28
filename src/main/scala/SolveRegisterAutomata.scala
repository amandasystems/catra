package uuverifiers.parikh_theory
import ap.SimpleAPI
import java.math.BigInteger
import scala.util.{Success, Failure, Try}
import scala.io.Source

sealed trait Result {
  val name: String
  val counterValues: Map[Counter, BigInteger] = Map.empty
}
case class Sat(assignments: Map[Counter, BigInteger]) extends Result {
  override val name = "sat"
  override val counterValues = assignments
}
case object Unsat extends Result {
  override val name = "unsat"

}
case object OutOfMemory extends Result {
  override val name = "memory-out"
}
case class Timeout(timeout_ms: Long) extends Result {
  override lazy val name = s"timeout > ${timeout_ms}ms"

}

object SolveRegisterAutomata extends App with Tracing {
  import fastparse.Parsed
  // TODO mode: get the image as a presburger formula

  def solveSatisfy(
      instance: Instance,
      arguments: CommandLineOptions
  ): Try[Result] = {
    val theories = instance.automata.map(
      automataGroup =>
        new RegisterCounting(
          instance.counters,
          automataGroup,
          instance.transitionToOffsets
        )
    )
    SimpleAPI.withProver { p =>
      // Needs to happen first because it may affect order?
      theories.foreach(p addTheory _)

      val counterToSolverConstant = instance.counters
        .map(c => (c, p.createConstantRaw(c.name)))
        .toMap

      implicit val o = p.order

      for (constraint <- instance.constraints) {
        p.addAssertion(
          trace("add constraint")(constraint toPrincess counterToSolverConstant)
        )
      }

      for (theory <- theories) {
        val isInImage = theory allowsMonoidValues instance.counters.map(
          counterToSolverConstant(_)
        )
        p.addAssertion(isInImage)
      }

      import SimpleAPI.ProverStatus

      p.checkSat(block = false)
      val satStatus = arguments.timeout_ms match {
        case Some(timeout_ms) => p.getStatus(timeout = timeout_ms)
        case None             => p.getStatus(block = true)
      }

      satStatus match {
        case ProverStatus.Sat | ProverStatus.Valid => {
          Success(
            Sat(
              instance.counters
                .map(c => c -> p.eval(counterToSolverConstant(c)).bigIntValue)
                .toMap
            )
          )
        }
        case ProverStatus.Unsat       => Success(Unsat)
        case ProverStatus.Running     => Success(Timeout(arguments.timeout_ms.get))
        case ProverStatus.OutOfMemory => Success(OutOfMemory)
        case otherStatus =>
          Failure(new Exception(s"unexpected solver status: ${otherStatus}"))
      }
    }
  }

  def measureTime[T](operation: => T): (T, Double) = {
    val start = System.nanoTime()
    val result = operation
    val elapsed = (System.nanoTime() - start).toDouble / 1_000_000_000
    (result, elapsed)
  }

  def fatalError(reason: Throwable) = {
    Console.err.println(reason.getMessage())
    sys.exit(1)
  }

  def reportRun(
      instanceFile: String,
      result: Try[Result],
      runtime: Double,
      parsetime: Double
  ): Unit = {
    result match {
      case Success(result) => {
        println(
          s"==== ${instanceFile}: ${result.name} run: ${runtime}s parse: ${parsetime}s ===="
        )
        result.counterValues.foreach {
          case (c, value) => println(s"${c.name} = ${value}")
        }
      }
      case Failure(reason) =>
        println(s"==== ${instanceFile} error: ${reason.getMessage()} ===")
    }

  }

  CommandLineOptions.parse(args) match {
    case Success(arguments) => {
      for (fileName <- arguments.inputFiles) {
        val fileContents = Source.fromFile(fileName).mkString("")
        val (parsed, parseTime) = measureTime(
          InputFileParser.parse(fileContents)
        )
        val (result, runtime) = measureTime {
          parsed match {
            case Parsed.Success(instance, _) => {
              // TODO also catch internal errors here!
              solveSatisfy(instance, arguments)
            }
            case Parsed.Failure(expected, _, extra) => {
              Console.err.println(s"E: parse error ${expected}")
              Console.err.println(s"E: ${extra.trace().longMsg}")
              Failure(new Exception(s"parse error: ${extra.trace().longMsg}"))
            }
          }
        }
        reportRun(fileName, result, runtime, parseTime)
      }
    }
    case Failure(reason) => fatalError(reason)
  }
}
