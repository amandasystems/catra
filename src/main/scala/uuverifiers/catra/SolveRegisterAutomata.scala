package uuverifiers.catra
import java.math.BigInteger
import scala.util.{Success, Failure, Try}
import scala.io.Source
import uuverifiers.common.Tracing

sealed trait Result {
  val name: String
  def printRepresentation(): Unit = {}
}
sealed trait SatisfactionResult extends Result {
  val counterValues: Map[Counter, BigInteger] = Map.empty

  override def printRepresentation(): Unit = {
    counterValues.foreach {
      case (c, value) => println(s"${c.name} = $value")
    }
  }
}

sealed trait ImageResult extends Result {
  val presburgerImage: Formula = TrueOrFalse(false)
}
case class Sat(assignments: Map[Counter, BigInteger])
    extends SatisfactionResult {
  override val name = "sat"
  override val counterValues: Map[Counter, BigInteger] = assignments
}
case object Unsat extends SatisfactionResult with ImageResult {
  override val name = "unsat"

}
case object OutOfMemory extends SatisfactionResult with ImageResult {
  override val name = "memory-out"
}
case class Timeout(timeout_ms: Long)
    extends SatisfactionResult
    with ImageResult {
  override lazy val name = s"timeout > ${timeout_ms}ms"

}

trait Backend {
  def solveSatisfy(instance: Instance): Try[SatisfactionResult]
  def findImage(instance: Instance): Try[ImageResult]
}

object SolveRegisterAutomata extends App with Tracing {
  import fastparse.Parsed

  def measureTime[T](operation: => T): (T, Double) = {
    val start = System.nanoTime()
    val SatisfactionResult = operation
    val elapsed = (System.nanoTime() - start).toDouble / 1_000_000_000
    (SatisfactionResult, elapsed)
  }

  def fatalError(reason: Throwable) = {
    Console.err.println(reason.getMessage)
    sys.exit(1)
  }

  def reportRun(
      instanceFile: String,
      result: Try[Result],
      runtime: Double,
      parsetime: Double
  ): Unit = {
    result match {
      case Success(result) =>
        println(
          s"==== $instanceFile: ${result.name} run: ${runtime}s parse: ${parsetime}s ===="
        )
        result.printRepresentation()
      case Failure(reason) =>
        println(s"==== $instanceFile error: ${reason.getMessage} ===")
        reason.printStackTrace()
    }
  }

  def runInstance(
      instance: Instance,
      arguments: CommandLineOptions
  ): Try[Result] = {
    arguments.dumpGraphvizDir.foreach { dir =>
      instance.automataProducts.zipWithIndex.foreach {
        case (group, groupIdx) =>
          group.zipWithIndex.foreach {
            case (automaton, autIdx) =>
              automaton.dumpDotFile(
                dir,
                s"input-automaton-$groupIdx-$autIdx.dot"
              )
            // TODO also annotate the automata with their counters, use real
            // state names!
          }
      }
    }
    arguments.runMode match {
      case FindImage    => arguments.getBackend().findImage(instance)
      case SolveSatisfy => arguments.getBackend().solveSatisfy(instance)
    }
  }

  def runInstances(arguments: CommandLineOptions): Unit = {
    for (fileName <- arguments.inputFiles) {
      val inputFileHandle = Source.fromFile(fileName)
      val fileContents = inputFileHandle.mkString("")
      inputFileHandle.close()
      val (parsed, parseTime) = measureTime(
        InputFileParser.parse(fileContents)
      )
      val (result, runtime) = measureTime {
        parsed match {
          case Parsed.Success(instance, _) =>
            instance.validate() match {
              case Valid => runInstance(instance, arguments)
              case Invalid(motivation) =>
                Failure(new Exception(s"Invalid input: $motivation"))
            }
          case Parsed.Failure(expected, _, extra) =>
            Console.err.println(s"E: parse error $expected")
            Console.err.println(s"E: ${extra.trace().longMsg}")
            Failure(new Exception(s"parse error: ${extra.trace().longMsg}"))
        }
      }
      reportRun(fileName, result, runtime, parseTime)
    }
  }

  CommandLineOptions.parse(args) match {
    case Success(arguments) => runInstances(arguments)
    case Failure(reason)    => fatalError(reason)
  }
}
