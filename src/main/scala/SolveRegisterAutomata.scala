package uuverifiers.parikh_theory
import ap.SimpleAPI

object SolveRegisterAutomata extends App {
  import fastparse.Parsed.{Failure, Success}
  // TODO mode: get the image as a presburger formula
  // TODO ensure register offsets are on disjoint transitions

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
        println(constraint)
        println(constraint.toPrincess (counterToSolverConstant))
        p.addAssertion(constraint toPrincess counterToSolverConstant)
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

  val result = InputFileParser.parse(Source.fromFile("input").mkString(""))

  // TODO some sort of monadised failure management here?
  result match {
    case Success(instance, _) => {
      solveSatisfy(instance)
    }
    case Failure(expected, _, extra) => {
      println(expected)
      println(extra.trace().longMsg)
    }
  }
}
