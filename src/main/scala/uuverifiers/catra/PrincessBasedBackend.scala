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

  // hack to collect all formulas sent to the prover
  val formulasInSolver = new ArrayBuffer[Conjunction]

  def withProver[T](f: SimpleAPI => T): T =
    dumpSMTDir match {
      case None => SimpleAPI.withProver(f)
      case Some(dumpDir) =>
        SimpleAPI.withProver(dumpSMT = true, dumpDirectory = dumpDir)(f)
    }

  override def findImage(instance: Instance): Try[ImageResult] = withProver {
    p =>
      arguments
        .runWithTimeout(p) {
          val counterToSolverConstant = prepareSolver(p, instance)
          ap.util.Debug.enableAllAssertions(false)

          val completeFormula = Conjunction.conj(formulasInSolver, p.order)
//      println(completeFormula)

          val qeProver = new IterativeQuantifierElimProver(p.theories, p.order)
          val reducer = ReduceWithConjunction(Conjunction.TRUE, p.order)

          var disjuncts: List[Conjunction] = List()
          var cont = true
          while (cont) {
            ap.util.Timeout.check

            val formulaToSolve =
              reducer(Conjunction.conj(completeFormula :: disjuncts, p.order))
            val nextDisjunct = qeProver(!formulaToSolve)

            println(nextDisjunct)

            if (nextDisjunct.isTrue)
              cont = false
            else
              disjuncts = nextDisjunct :: disjuncts
          }

          if (disjuncts.isEmpty) {
            Unsat
          } else {
            val image = reducer(!Conjunction.conj(disjuncts, p.order))
            new ImageResult {
              override val presburgerImage
                  : Formula = TrueOrFalse(false) // FIXME
              override val name: String = "non-empty image " + p.pp(
                p.asIFormula(image)
              )
            }
          }

          /*
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
         */
        }

  }

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
      withProver { p =>
        arguments.runWithTimeout(p) {
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
}
