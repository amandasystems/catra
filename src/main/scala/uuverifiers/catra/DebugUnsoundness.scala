package uuverifiers.catra

import uuverifiers.catra.SolveRegisterAutomata.measureTime
import uuverifiers.common.{Automaton, Tracing}

import scala.annotation.tailrec
import scala.collection.mutable
import scala.math.Ordered.orderingToOrdered
import scala.util.{Failure, Success}

sealed case class Score(nrUnsat: Int, nrTimeouts: Int) extends Ordered[Score] {

  def +(other: Score): Score =
    Score(this.nrUnsat + other.nrUnsat, this.nrTimeouts + other.nrTimeouts)

  def compare(that: Score): Int =
    (this.nrUnsat, this.nrTimeouts) compare (that.nrUnsat, that.nrTimeouts)
}

sealed case class Configuration(
    instance: Instance,
    configuration: CommandLineOptions
) extends Ordered[Configuration]
    with Tracing {

  private val giveUpAtSeed = 5
  private val nrTimesToEvaluate = 5

  def withRandomSeed(newSeed: Int): Configuration =
    if (newSeed == configuration.randomSeed) this
    else this.copy(configuration = configuration.withRandomSeed(newSeed))

  def findBestSeed(): Configuration = {
    var currentSeed = 1

    optimiseConfiguration(
      bestSoFar =>
        if (currentSeed >= giveUpAtSeed) {
          None
        } else {
          val newConfig =
            bestSoFar.withRandomSeed(trace("Trying seed")(currentSeed))
          currentSeed += 1
          Some(newConfig)
        }
    )
  }

  def writeToFile(fileName: String): Unit = {
    import java.io.{BufferedWriter, File, FileWriter}

    val bw = new BufferedWriter(new FileWriter(new File(fileName)))
    // TODO
    bw.write(this.configuration.toString)
    bw.write(this.instance.toString)
    bw.close()
  }

  this.enableTracing()

  val nrAutomata: Int = instance.automataProducts.map(_.size).sum

  private def runOnce(): Score = {
    configuration.getBackend().solveSatisfy(instance) match {
      case Failure(_) | Success(Sat(_))               => Score(0, 0)
      case Success(Unsat)                             => Score(1, 0)
      case Success(OutOfMemory) | Success(Timeout(_)) => Score(0, 1)
    }
  }

  lazy val evaluate: Score =
    trace("final score: ")(
      (1 to nrTimesToEvaluate)
        .map(_ => runOnce())
        .foldRight(Score(0, 0))(_ + _)
    )

  private def dropAutomata(
      automataProducts: Seq[Seq[Automaton]],
      automataSelected: IndexedSeq[mutable.IndexedSeq[Option[Boolean]]]
  ): ((Int, Int), Seq[Seq[Automaton]]) = {
    // find the first unknown and try excluding it
    val selectedProduct =
      automataSelected.indexWhere(p => p.exists(_.isEmpty))
    val selectedAutomaton =
      automataSelected(selectedProduct).indexWhere(_.isEmpty)

    val prunedAutomata = automataProducts.zipWithIndex.map {
      case (as, pi) =>
        as.zipWithIndex
          .filterNot {
            case (_, ai) =>
              (ai == selectedAutomaton && pi == selectedProduct) || automataSelected(
                pi
              )(ai).contains(false)
          }
          .map(_._1)
    }
    ((selectedProduct, selectedAutomaton), prunedAutomata)
  }

  private def optimiseConfiguration(
      tryImprove: Configuration => Option[Configuration]
  ): Configuration = {

    var bestConfig = this
    var nextCandidate = tryImprove(bestConfig)

    while (nextCandidate.isDefined) {
      val candidate = nextCandidate.get
      if (candidate > bestConfig) {
        bestConfig = candidate
      }
      nextCandidate = tryImprove(bestConfig)
    }

    bestConfig
  }

  def minimiseInstance(): Configuration = {
    println("Starting instance minimisation...")
    val notTried: Option[Boolean] = None

    val automataSelected: IndexedSeq[mutable.IndexedSeq[Option[Boolean]]] =
      instance.automataProducts
        .map(p => mutable.IndexedSeq.fill(p.size)(notTried))
        .toIndexedSeq

    optimiseConfiguration { _ =>
      if (automataSelected.flatten.exists(_.isEmpty)) {
        val ((pi, ai), filteredProducts) =
          dropAutomata(instance.automataProducts, automataSelected)

        val currentName = instance.automataProducts(pi)(ai).name
        println(s"Removing $currentName...")
        Some(
          this.copy(
            instance = instance.copy(automataProducts = filteredProducts)
          )
        )
      } else None
    }
  }

  def tweakRestartiness(): Configuration = {
    val timeoutStep = 10
    var currentFactor = configuration.restartTimeoutFactor
    optimiseConfiguration { bestSoFar =>
      if (currentFactor <= 1) {
        None
      } else {
        val candidateFactor = currentFactor - timeoutStep
        currentFactor = candidateFactor max 1
        Some(
          bestSoFar.copy(
            configuration = bestSoFar.configuration.withRestartTimeoutFactor(
              trace("Trying restart factor")(currentFactor)
            )
          )
        )
      }
    }
  }

  def compare(that: Configuration): Int =
    (this.evaluate, this.nrAutomata) compare (that.evaluate, that.nrAutomata)
}

object DebugUnsoundness {

  private val nrTriesBeforeAssumedSound = 20

  @tailrec
  def hasUnsoundness(
      backend: LazyBackend,
      instance: Instance,
      iteration: Int = 0
  ): Boolean =
    if (iteration >= nrTriesBeforeAssumedSound) {
      println(s"\nGave up finding unsoundness after $iteration tries!")
      false
    } else {
      val (result, runtime) = measureTime(backend solveSatisfy instance)
      result match {
        case Success(Unsat) =>
          println(s"Found unsound result after $iteration tries!")
          true
        case Success(Timeout(_)) =>
          print("⏰")
          hasUnsoundness(backend, instance, iteration + 1)
        case Success(Sat(_)) =>
          print(s"❌(${runtime.round}s)")
          hasUnsoundness(backend, instance, iteration + 1)
      }
    }

  def optimiseReproducability(
      instances: Seq[Instance],
      config: CommandLineOptions
  ): Configuration =
    instances
      .map(Configuration(_, config).findBestSeed())
      .max
      .tweakRestartiness()
      .minimiseInstance()
}
