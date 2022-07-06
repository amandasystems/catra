package uuverifiers.catra

import ap.{PresburgerTools, SimpleAPI}
import ap.SimpleAPI.ProverStatus
import ap.basetypes.LeftistHeap
import ap.parser.IFormula
import ap.terfor.TerForConvenience.conj
import ap.terfor.conjunctions.Conjunction
import ap.terfor.{ConstantTerm, TermOrder}
import uuverifiers.common.Tex.formulaToTex
import uuverifiers.common.{Automaton, NrTransitionsOrdering}
import uuverifiers.parikh_theory.VariousHelpers.transitionsIncrementRegisters

import java.io.{BufferedWriter, File, FileWriter}
import scala.annotation.tailrec
import scala.util.Try

private class ProductQueue(private val queue: LeftistHeap[Automaton, _]) {
  def enqueue(a: Automaton): ProductQueue = new ProductQueue(queue + a)
  def isEmpty: Boolean = queue.isEmpty
}

private object ProductQueue {
  def apply(automata: Iterable[Automaton]) =
    new ProductQueue(
      LeftistHeap.EMPTY_HEAP(ord = NrTransitionsOrdering) ++ automata
    )
  def unapply(q: ProductQueue): Option[(Automaton, Automaton, ProductQueue)] = {
    if (q.queue.size >= 2) {
      val first = q.queue.findMin
      val rest1 = q.queue.deleteMin
      val second = rest1.findMin
      Some((first, second, new ProductQueue(rest1.deleteMin)))
    } else None
  }
}
class BaselineBackend(override val arguments: CommandLineOptions)
    extends PrincessBasedBackend {

  override def findImage(instance: Instance): Try[ImageResult] =
    arguments.withProver { p =>
      val counterToSolverConstant =
        trace("Counter -> solver constant")(
          instance.counters.map(c => c -> c.toConstant(p)).toMap
        )

      implicit val order: TermOrder = p.order

      val constraints = conj(
        instance.constraints
          .map(c => p.asConjunction(c.toPrincess(counterToSolverConstant)))
      )

      def parikhImage(group: Seq[Automaton]): Conjunction =
        group
          .reduceOption(_ productWith _)
          .map(
            product =>
              product.parikhImage(
                transitionsIncrementRegisters(product, counterToSolverConstant)(
                  _
                ),
                quantElim = false
              )
          )
          .getOrElse(Conjunction.TRUE)

      val image =
        p.asIFormula(
          PresburgerTools.elimQuantifiersWithPreds(
            conj(constraints +: instance.automataProducts.map(parikhImage))
          )
        )

      if (image.isFalse) Unsat
      else
        new ImageResult {
          override val presburgerImage: Formula = TrueOrFalse(false) // FIXME
          override val name: String = s"non-empty image $image" // FIXME
        }
    }

  def handleDumpingGraphviz(a: Automaton): Unit =
    arguments.dumpGraphvizDir.foreach(
      dir => a.dumpDotFile(dir, s"${a.name}.dot")
    )

  private def handleDumpingFlow(a: Automaton, eq: IFormula): Unit =
    arguments.dumpEquationDir.foreach { dir =>
      val file = new FileWriter(new File(dir, s"${a.name}.flow.tex"))
      val bw = new BufferedWriter(file)
      bw.write(formulaToTex(eq))
      bw.close()
    }

  private def logDecision(msg: String): Unit = if (arguments.printDecisions) {
    System.err.println(msg)
  }

  @tailrec
  final private def incrementallyMaterialiseProducts(
      p: SimpleAPI,
      counterToSolverConstant: Map[Counter, ConstantTerm],
      satStatus: SimpleAPI.ProverStatus.Value,
      productsLeft: Seq[Seq[Automaton]]
  ): Unit = (productsLeft, satStatus) match {
    case (_, ProverStatus.Unsat) => ()
    case (Seq(), _)              => ()
    case (terms +: remainingProducts, _) =>
      incrementallyComputeProduct(
        p,
        counterToSolverConstant,
        ProductQueue(terms)
      )
      incrementallyMaterialiseProducts(
        p,
        counterToSolverConstant,
        p.checkSat(block = true),
        remainingProducts
      )
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

    val termsToCheckSat = if (arguments.checkTermSat) {
      instance.automataProducts.flatten
    } else Seq()

    incrementallyMaterialiseProducts(
      p,
      counterToSolverConstant,
      satStatus = checkTermsCoherent(
        p,
        counterToSolverConstant,
        termsToCheckSat
      ),
      instance.automataProducts
    )

    counterToSolverConstant
  }

  @tailrec
  private def checkTermsCoherent(
      p: SimpleAPI,
      counterToSolverConstant: Map[Counter, ConstantTerm],
      remainingTerms: Seq[Automaton]
  ): SimpleAPI.ProverStatus.Value = remainingTerms match {
    case Seq() => p.checkSat(block = true)
    case fst +: rest =>
      postParikhSat(p, counterToSolverConstant, fst)
      val satStatus = trace("term SAT check")(
        p.checkSat(block = true)
      )
      logDecision(s"Term ${fst.name} satisfiable? $satStatus")
      if (satStatus != ProverStatus.Unsat) {
        checkTermsCoherent(p, counterToSolverConstant, rest)
      } else {
        satStatus
      }
  }

  private def postParikhSat(
      p: SimpleAPI,
      counterToSolverConstant: Map[Counter, ConstantTerm],
      newProduct: Automaton
  ): Unit = {
    implicit val order: TermOrder = p.order
    val parikhImageIsConsistent = trace("partial product Parikh image")(
      newProduct.parikhImage(
        transitionsIncrementRegisters(newProduct, counterToSolverConstant)(_),
        quantElim = arguments.eliminateQuantifiers
      )
    )

    handleDumpingFlow(newProduct, p asIFormula parikhImageIsConsistent)
    p.addAssertion(parikhImageIsConsistent)
  }

  private def computeProductStep(
      left: Automaton,
      right: Automaton
  ): Automaton = {
    val newProduct = left productWith right
    handleDumpingGraphviz(newProduct)
    ap.util.Timeout.check
    newProduct
  }

  @tailrec
  private def incrementallyComputeProduct(
      p: SimpleAPI,
      counterToSolverConstant: Map[Counter, ConstantTerm],
      automataLeft: ProductQueue
  ): Unit = automataLeft match {
    case ProductQueue(first, second, rest) =>
      val product = computeProductStep(first, second)

      logDecision(
        s"""Computed product ${product.name}.
           |\tSize of terms: ${first.transitions.size}, ${second.transitions.size}
           |\tSize of product: ${product.transitions.size}""".stripMargin
      )

      val stillSatisfiable =
        if (rest.isEmpty || arguments.checkIntermediateSat) {
          postParikhSat(p, counterToSolverConstant, product)
          val stillSatisfiable = trace("product SAT check")(
            p.checkSat(block = true)
          ) != ProverStatus.Unsat
          logDecision(s"Satisfiable? $stillSatisfiable")
          stillSatisfiable
        } else {
          true
        }

      if (stillSatisfiable) {
        incrementallyComputeProduct(
          p,
          counterToSolverConstant,
          rest.enqueue(product)
        )
      }
    case _ =>
  }
}
