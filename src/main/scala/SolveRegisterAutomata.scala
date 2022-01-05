package uuverifiers.parikh_theory
import ap.SimpleAPI
import scala.util.{Success, Failure, Try}

object SolveRegisterAutomata extends App with Tracing {
  import fastparse.Parsed.{Failure, Success}
  // TODO mode: get the image as a presburger formula

  def solveSatisfy(instance: Instance) = {

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

      import SimpleAPI.ProverStatus._

      val satStatus = p.checkSat(true)
      println(satStatus.toString.toLowerCase())
      // TODO use this to signal exit status
      satStatus match {
        case Sat | Valid => {
          for (c <- instance.counters) {
            println(s"${c.name} = ${p.eval(counterToSolverConstant(c))}")
          }
        }
        0
      case Unsat                             => 0
        case OutOfMemory | Running | Unknown => ???
        case Error | Inconclusive | Invalid  => ???
      }
    }

  }

  // how do we parse command line options???
  // https://stackoverflow.com/questions/2315912/best-way-to-parse-command-line-parameters
  import scala.io.Source

  val arguments = CommandLineOptions.parse(args).get

  for (fileName <- arguments.inputFiles) {
    val fileContents = Source.fromFile(fileName).mkString("")
    println(fileName)
    val parseStart = System.nanoTime()
    val parsed = InputFileParser.parse(fileContents)
    val parseTime = (System.nanoTime() - parseStart).toDouble / 1_000_000_000
    val runStart = System.nanoTime()
    parsed match {
      case Success(instance, _) => {
        solveSatisfy(instance)
      }
      case Failure(expected, _, extra) => {
        println(expected)
        println(extra.trace().longMsg)
      }
    }
    val runtime = (System.nanoTime() - runStart).toDouble / 1_000_000_000
    println(s"==== run: ${runtime}s parse: ${parseTime}s ====")

  }
}
