package uuverifiers.catra

import uuverifiers.common.AutomataTypes.Transition
import uuverifiers.common.Automaton
import ap.SimpleAPI
import SimpleAPI.ProverStatus
import ap.terfor.TerForConvenience.{l => toLinearCombination}
import ap.basetypes.IdealInt
import ap.terfor.ConstantTerm
import scala.annotation.tailrec

class VermaBackend(override val arguments: CommandLineOptions)
    extends PrincessBasedBackend {

  override def prepareSolver(
      p: SimpleAPI,
      instance: Instance
  ): Map[Counter, ConstantTerm] = {
    import ap.terfor.TerForConvenience._
    import p._

    val counterToSolverConstant =
      trace("Counter -> solver constant")(
        instance.counters
          .map(c => c -> p.createConstantRaw(c.name))
          .toMap
      )

    implicit val o = order // This needs to happen after the constant creation.

    for (constraint <- instance.constraints) {
      p.addAssertion(
        trace("post constraint from input file")(
          constraint toPrincess counterToSolverConstant
        )
      )
    }

    instance.automata.foreach { terms =>
      var productStep = 0

      var productSoFar: Automaton = terms.head
      var productTransitionToOffsets =
        trace("transition to offsets at start")(instance.transitionToOffsets)

      // productSoFar.dumpDotFile(s"verma-product-step-${productStep}.dot")

      def incrementOf(counter: Counter, transition: Transition) =
        trace(s"${transition} increments ${counter} to") {
          IdealInt.int2idealInt(
            productTransitionToOffsets(transition).getOrElse(counter, 0)
          )
        }

      def computeProductStep(term: Automaton): Unit = {
        val newProduct = productSoFar productWithSources term
        productStep += 1
        // term.dumpDotFile(s"verma-product-term-${productStep}.dot")
        // newProduct.dumpDotFile(s"verma-product-step-${productStep}.dot")

        productSoFar = newProduct.product
        ap.util.Timeout.check

        productTransitionToOffsets =
          trace("transition to offsets after product") {
            productSoFar.transitions.map { productTransition =>
              val (partialProductTransition, termTransition) =
                newProduct.originOfTransition(productTransition)

              trace("originating transitions")(
                (partialProductTransition, termTransition)
              )

              val counterIncrements = trace("left counter increments")(
                instance
                  .transitionToOffsets(termTransition)
              ) ++ trace("right counter increments")(
                productTransitionToOffsets(
                  partialProductTransition
                )
              )

              productTransition -> counterIncrements
            }.toMap
          }

        val affectedCounters =
          productTransitionToOffsets.values.flatMap(_.keys).toSet

        // This enforces the bridging clause: c  = SUM t : sigma(t) * increment(c, t)
        // NOTE:  We need to iterate over only the counters occurring in the
        // partial product, or any counters appearing in later products will be
        // forced to 0.
        def transitionsIncrementRegisters(
            sigma: Map[Transition, ap.terfor.Term]
        ) =
          trace(s"binding clauses: counters are coherent:") {
            conj(affectedCounters.map { counter =>
              val c = counterToSolverConstant(counter)

              val incrementAndNrTaken =
                productSoFar.transitions.map { transition =>
                  (
                    incrementOf(counter, transition),
                    toLinearCombination(sigma(transition))
                  )
                }

              c === sum(incrementAndNrTaken)
            })
          }

        p.addAssertion(
          trace("partial product Parikh image")(
            productSoFar.parikhImage(
              transitionsIncrementRegisters(_),
              quantElim = false
            )(order)
          )
        )
      }

      @tailrec
      def incrementallyComputeProduct(automataLeft: Seq[Automaton]): Unit =
        automataLeft match {
          case Seq() => ()
          case term +: rest => {
            computeProductStep(term)
            val stillSatisfiable = trace("product SAT check")(
              p.checkSat(block = true)
            ) != ProverStatus.Unsat
            if (stillSatisfiable) {
              incrementallyComputeProduct(rest)
            }
          }
        }

      incrementallyComputeProduct(terms.tail)

    }
    counterToSolverConstant
  }
}
