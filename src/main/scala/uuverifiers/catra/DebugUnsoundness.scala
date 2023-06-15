package uuverifiers.catra

import uuverifiers.common.Tracing

import scala.collection.mutable
import scala.math.Ordered.orderingToOrdered
import scala.util.{Failure, Success}

trait Optimiser extends Tracing {
  val startingConfiguration: Configuration

  enableTracing(true)

  def reportResult(didImprove: Boolean): Unit
  def canImprove(): Boolean
  def nextCandidate(): Configuration

  def optimise(): Configuration = {
    var bestConfig = startingConfiguration

    while (canImprove()) {
      val candidate = nextCandidate()
      val didImprove = candidate > bestConfig
      if (didImprove) {
        trace("New best config!")()
        bestConfig = candidate
      }
      reportResult(didImprove)
    }
    bestConfig
  }
}

sealed case class Score(nrUnsat: Int, nrTimeouts: Int) extends Ordered[Score] {

  def +(other: Score): Score =
    Score(this.nrUnsat + other.nrUnsat, this.nrTimeouts + other.nrTimeouts)

  def compare(that: Score): Int =
    (this.nrUnsat, this.nrTimeouts) compare (that.nrUnsat, that.nrTimeouts)
}

object Configuration {
  private val giveUpAtSeed = 5
  private val nrTimesToEvaluate = 30

}

sealed case class Configuration(
    instance: Instance,
    configuration: CommandLineOptions
) extends Ordered[Configuration]
    with Tracing { self =>

  def withRandomSeed(newSeed: Int): Configuration =
    if (newSeed == configuration.randomSeed) this
    else this.copy(configuration = configuration.withRandomSeed(newSeed))

  def findBestSeed(): Configuration = {
    new Optimiser {
      private var currentSeed = 1
      override val startingConfiguration: Configuration = self
      override def reportResult(didImprove: Boolean): Unit = {
        if (didImprove) trace("seed was an improvement!")(currentSeed)
        currentSeed += 1
      }
      override def canImprove(): Boolean =
        currentSeed < Configuration.giveUpAtSeed
      override def nextCandidate(): Configuration =
        startingConfiguration.withRandomSeed(currentSeed)
    }.optimise()
  }

  def writeToFile(fileName: String): Unit = {
    import java.io.{BufferedWriter, File, FileWriter}

    val bw = new BufferedWriter(new FileWriter(new File(fileName)))
    // TODO
    bw.write("/* Configuration:")
    bw.write(this.configuration.toString)
    bw.write("*/\n\n")
    bw.write(this.instance.toString)
    bw.close()
  }

  this.enableTracing()

  val nrAutomata: Int = instance.automataProducts.map(_.size).sum

  private def runOnce(): Score = {
    configuration.getBackend.solveSatisfy(instance) match {
      case Failure(_) | Success(Sat(_))               => Score(0, 0)
      case Success(Unsat)                             => Score(1, 0)
      case Success(OutOfMemory) | Success(Timeout(_)) => Score(0, 1)
    }
  }

  lazy val evaluate: Score = trace("evaluate final score") {
    (1 to Configuration.nrTimesToEvaluate)
      .map(_ => runOnce())
      .foldRight(Score(0, 0))(_ + _)
  }

  def minimiseInstance(): Configuration = {
    new Optimiser {

      private val automataSelected =
        instance.automataProducts
          .map(p => mutable.IndexedSeq.fill(p.size)(false))
          .toIndexedSeq

      private var selectedProduct = 0
      private var selectedAutomaton = 0
      private var exhausted = false

      private def currentProduct(): mutable.IndexedSeq[Boolean] =
        automataSelected(selectedProduct)

      private def wrapAroundOrStop() = {
        if (selectedProduct < automataSelected.size - 1) {
          selectedProduct += 1
          selectedAutomaton = 0
        } else { // Unable to wrap around!
          exhausted = true
        }
      }

      private def incrementSelection() = {
        if (selectedAutomaton < currentProduct().size - 1)
          selectedAutomaton += 1
        else wrapAroundOrStop()
      }

      override val startingConfiguration: Configuration = self
      override def reportResult(didImprove: Boolean): Unit = {
        automataSelected(selectedProduct)(selectedAutomaton) = !didImprove
        incrementSelection()

      }
      override def canImprove(): Boolean = !exhausted
      override def nextCandidate(): Configuration = {
        val filteredProducts =
          startingConfiguration.instance.automataProducts.zipWithIndex.map {
            case (as, pi) =>
              as.zipWithIndex
                .filterNot {
                  case (_, ai) =>
                    ai == selectedAutomaton && pi == selectedProduct
                }
                .map(_._1)
          }

        startingConfiguration.copy(
          instance = instance.copy(automataProducts = filteredProducts)
        )
      }
    }.optimise()
  }

  def tweakRestartiness(): Configuration = {
    val timeoutStep = 10
    new Optimiser {
      private var currentFactor = configuration.restartTimeoutFactor

      override val startingConfiguration: Configuration = self
      override def reportResult(didImprove: Boolean): Unit = {}
      override def canImprove(): Boolean = currentFactor > 1
      override def nextCandidate(): Configuration = {
        val candidateFactor = currentFactor - timeoutStep
        currentFactor = candidateFactor max 1
        startingConfiguration.copy(
          configuration =
            startingConfiguration.configuration.withRestartTimeoutFactor(
              trace("Trying timeout factor")(currentFactor)
            )
        )

      }
    }.optimise()
  }

  def compare(that: Configuration): Int =
    (this.evaluate, this.nrAutomata) compare (that.evaluate, that.nrAutomata)
}

object DebugUnsoundness {
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
