package uuverifiers.catra

import fastparse.Parsed
import uuverifiers.catra.SolveRegisterAutomata.measureTime
import uuverifiers.common.Automaton

import scala.annotation.tailrec
import scala.collection.mutable
import scala.io.Source
import scala.util.Success

object DebugUnsoundness {
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
