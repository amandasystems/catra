package uuverifiers.catra

import uuverifiers.common.AutomataTypes.Transition
import uuverifiers.common.Automaton
import ap.SimpleAPI
import SimpleAPI.ProverStatus
import ap.terfor.TerForConvenience.{l => toLinearCombination}
import ap.basetypes.IdealInt
import ap.terfor.ConstantTerm
import scala.util.Try
import uuverifiers.parikh_theory.TryButThrowTimeouts

class VermaBackend(override val arguments: CommandLineOptions)
    extends PrincessBasedBackend {

  override def prepareSolver(
      p: SimpleAPI,
      instance: Instance
  ): Try[Map[Counter, ConstantTerm]] = TryButThrowTimeouts {
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
      var productSoFar: Automaton = terms.head
      var productTransitionToOffsets = instance.transitionToOffsets
      // This enforces the bridging clause: c  = SUM t : sigma(t) * increment(c, t)
      // NOTE:  We need to iterate over only the live counters, because the
      // counters that were initially not mentioned by any automaton need to be
      // left without constraints and would otherwise be set to zero, despite
      // being unconstrained by the automata.

      def transitionsIncrementRegisters(
          sigma: Map[Transition, ap.terfor.Term]
      ) =
        trace(s"binding clauses: counters are coherent:")(
          conj(instance.liveCounters.map { counter =>
            counterToSolverConstant(counter) === sum(
              productSoFar.transitions.map { transition =>
                (
                  IdealInt.int2idealInt(
                    productTransitionToOffsets(transition)
                      .getOrElse(counter, 0)
                  ),
                  toLinearCombination(sigma(transition))
                )
              }
            )
          })
        )

      def computeProductStep(term: Automaton): Unit = {
        val newProduct = productSoFar productWithSources term
        productSoFar = newProduct.product
        ap.util.Timeout.check

        productTransitionToOffsets = productSoFar.transitions.map {
          productTransition =>
            val (partialProductTransition, termTransition) =
              newProduct.originOfTransition(productTransition)

            val counterIncrements = instance
              .transitionToOffsets(termTransition) ++ productTransitionToOffsets(
              partialProductTransition
            )

            productTransition -> counterIncrements
        }.toMap

        p.addAssertion(
          trace("partial product Parikh image")(
            productSoFar.parikhImage(
              transitionsIncrementRegisters(_),
              quantElim = true
            )(order)
          )
        )
      }

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
