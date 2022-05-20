package uuverifiers.catra

import uuverifiers.common.{Automaton, GraphvizDumper, NrTransitionsOrdering}
import ap.SimpleAPI
import SimpleAPI.ProverStatus
import ap.basetypes.LeftistHeap
import ap.terfor.{ConstantTerm, TermOrder}
import uuverifiers.parikh_theory.VariousHelpers.transitionsIncrementRegisters

import scala.annotation.tailrec

class VermaBackend(override val arguments: CommandLineOptions)
    extends PrincessBasedBackend {

  def handleDumpingGraphviz(a: GraphvizDumper, fileName: String): Unit =
    arguments.dumpGraphvizDir.foreach(dir => a.dumpDotFile(dir, fileName))

  private def logDecision(msg: String): Unit = if (arguments.printDecisions) {
    System.err.println(msg)
  }

  override def prepareSolver(
      p: SimpleAPI,
      instance: Instance
  ): Map[Counter, ConstantTerm] = {

    val counterToSolverConstant =
      trace("Counter -> solver constant")(
        instance.counters.map(c => c -> c.toConstant(p)).toMap
      )

    for (constraint <- instance.constraints) {
      p.addAssertion(
        trace("post constraint from input file")(
          constraint toPrincess counterToSolverConstant
        )
      )
    }

    instance.automataProducts.foreach(
      terms =>
        incrementallyComputeProduct(
          p,
          counterToSolverConstant,
          0,
          LeftistHeap.EMPTY_HEAP(ord = NrTransitionsOrdering) ++ terms
        )
    )
    counterToSolverConstant
  }

  private def postParikhSat(
      p: SimpleAPI,
      counterToSolverConstant: Map[Counter, ConstantTerm],
      newProduct: Automaton
  ): Unit = {
    implicit val order: TermOrder = p.order

    p.addAssertion(
      trace("partial product Parikh image")(
        newProduct.parikhImage(
          transitionsIncrementRegisters(newProduct, counterToSolverConstant)(_),
          quantElim = false
        )
      )
    )
  }

  private def computeProductStep(
      productStep: Int,
      left: Automaton,
      right: Automaton
  ): Automaton = {
    val newProduct = left productWith right
    handleDumpingGraphviz(left, s"verma-product-left-$productStep.dot")
    handleDumpingGraphviz(right, s"verma-product-right-$productStep.dot")
    handleDumpingGraphviz(newProduct, s"verma-product-step-$productStep.dot")
    ap.util.Timeout.check
    newProduct
  }

  @tailrec
  private def incrementallyComputeProduct(
      p: SimpleAPI,
      counterToSolverConstant: Map[Counter, ConstantTerm],
      productStep: Int,
      automataLeft: LeftistHeap[Automaton, _]
  ): Unit = if (automataLeft.size >= 2) {
    val first = automataLeft.findMin
    val rest1 = automataLeft.deleteMin
    val second = rest1.findMin
    val product = computeProductStep(productStep, first, second)

    logDecision(
      s"""Computed product step $productStep.
         |\tSize of terms: ${first.transitions.size}, ${second.transitions.size}
         |\tSize of product: ${product.transitions.size}""".stripMargin
    )

    postParikhSat(p, counterToSolverConstant, product)

    val stillSatisfiable = trace("product SAT check")(
      p.checkSat(block = true)
    ) != ProverStatus.Unsat

    logDecision(s"Satisfiable? $stillSatisfiable")
    if (stillSatisfiable) {
      incrementallyComputeProduct(
        p,
        counterToSolverConstant,
        productStep + 1,
        rest1.deleteMin + product
      )
    }
  }
}
