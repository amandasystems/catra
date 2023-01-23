package uuverifiers.catra

import fastparse.Parsed
import uuverifiers.catra.SolveRegisterAutomata.measureTime
import uuverifiers.common.Automaton

import scala.annotation.tailrec
import scala.collection.mutable
import scala.io.Source
import scala.util.Success
 import scala.math.Ordering.Implicits._


sealed case class Score(nrUnsat: Int, nrTimeouts: Int){
  def +(other: Score) = Score(this.nrUnsat + other.nrUnsat,
    this.nrTimeouts + other.nrTimeouts)

  def compareScore(that: Score): Int =  
  {
    val thisTuple = (this.nrUnsat, this.nrTimeouts)
    val thatTuple = (that.nrUnsat, that.nrTimeouts)
    if (thisTuple < thatTuple) {
      -1
    } else if(thatTuple == thisTuple) {0} else {1}
  }
  }



sealed case class Configuration(instance: Instance, configuration: CommandLineOptions) {
  
  val nrAutomata = instance.automataProducts.map(_.size).sum

  private def runOnce() = configuration.getBackend().solveSatisfy(instance) match {
    case ProverStatus.Sat => Score(0, 0)
    case ProverStatus.Unsat => Score(1, 0)
    case ProverStatus.Timeout => Score(0, 1)
  }
  
  lazy val evaluate = { 
    (1 to 20).map( _ => runOnce()).foldRight(Score(0,0))(_ + _)
  }

  // def withMoreRestarts() = Configuration(instance, configuration.withRestarts(configuration.restarts - 10))
  // def withSmallerInstance() = Configuration(DebugUnsoundness.minimiseInstance(instance), configuration)

  def compareConfig(that: Configuration): Int = {
    val evaluationComparison = this.evaluate compareScore that.evaluate

  if (evaluationComparison == 0) this.nrAutomata compare that.nrAutomata else evaluationComparison

  }

}

object DebugUnsoundness {

  def simplifyInstances(instances: Seq[Instance], config: CommandLineOptions): Instance = {
    val candidates = collection.mutable.PriorityQueue()(Ordering[Configuration].by(c => (c.evaluate, c.nrAutomata)))
    
    instances.foreach(i => candidates.enqueue(Configuration(i, config)))

    // FIXME: try first minimising restarts
    // FIXME then try minimising instances
   
    instances.head

  }

  val nrTriesBeforeAssumedSound = 20
  val timeoutMilliseconds = "120000"

  val Parsed.Success(unsoundInstance, _) = {
    val inputFile = "unsound/parikh-constraints-0.par"
    println(s"Starting soundness debugging for $inputFile")
    val inputFileHandle = Source.fromFile(inputFile)
    val instance = InputFileParser.parse(inputFileHandle.mkString(""))
    inputFileHandle.close()
    instance
  }

  val backend = new LazyBackend(
    CommandLineOptions
      .parse(
        Array(
          "solve-satisfy",
          "--timeout",
          timeoutMilliseconds
        )
      )
      .get
  )

  def dropAutomata(
      automataProducts: Seq[Seq[Automaton]],
      automataSelected: IndexedSeq[mutable.IndexedSeq[Option[Boolean]]]
  ): ((Int, Int), Seq[Seq[Automaton]]) = {
    // find the first unknown and try excluding it
    val selectedProduct = automataSelected.indexWhere(p => p.exists(_.isEmpty))
    val selectedAutomaton =
      automataSelected(selectedProduct).indexWhere(_.isEmpty)

    val selectionStr: String = automataSelected
      .map(
        p =>
          p.map {
            case None        => '?'
            case Some(true)  => '1'
            case Some(false) => '0'
          }.mkString
      )
      .mkString("\n")
    println(
      s"Selection Matrix: $selectionStr, trying ($selectedProduct,$selectedAutomaton)"
    )

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

  @tailrec
  def hasUnsoundness(instance: Instance, iteration: Int = 0): Boolean =
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
          hasUnsoundness(instance, iteration + 1)
        case Success(Sat(_)) =>
          print(s"❌(${runtime.round}s)")
          hasUnsoundness(instance, iteration + 1)
      }
    }

  val notTried: Option[Boolean] = None

  val automataSelected: IndexedSeq[mutable.IndexedSeq[Option[Boolean]]] =
    unsoundInstance.automataProducts
      .map(p => mutable.IndexedSeq.fill(p.size)(notTried))
      .toIndexedSeq

  println("Testing initial assumption...")
  hasUnsoundness(unsoundInstance)

  while (automataSelected.flatten.exists(_.isEmpty)) {
    val ((pi, ai), automataProducts) =
      dropAutomata(unsoundInstance.automataProducts, automataSelected)

    val currentInstance = Instance(
      counters = unsoundInstance.counters,
      constraints = unsoundInstance.constraints,
      automataProducts = automataProducts
    )
    val currentName = unsoundInstance.automataProducts(pi)(ai).name
    println(s"Removing $currentName, does that preserve unsoundness?")

    val unsoundnessFound = hasUnsoundness(currentInstance)
    if (unsoundnessFound) {
      println(s"Removing $currentName preserves unsoundness, removing it...")
    }
    automataSelected(pi)(ai) = Some(!unsoundnessFound)
  }
}
