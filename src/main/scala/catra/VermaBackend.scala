package uuverifiers.catra

import WhyCantIDefineGlobalTypeAliasesGoddammit.TransitionToCounterOffsets
import uuverifiers.common.AutomataTypes.Transition
import uuverifiers.common.Automaton
import ap.SimpleAPI
import ap.terfor.conjunctions.Conjunction
import ap.terfor.TerForConvenience.{l => toLinearCombination}
import ap.basetypes.IdealInt
import ap.terfor.ConstantTerm

sealed case class RecordKeepingProduct(
    transitionOrigins: Map[Transition, Seq[
      Transition
    ]],
    product: Automaton
) {
  def originalTransitions() = transitionOrigins.values.flatten
  def touchesCounter(
      c: Counter,
      transitionToOffsets: TransitionToCounterOffsets
  ) =
    originalTransitions().exists(transitionToOffsets(_) contains c)

}

class VermaBackend(override val arguments: CommandLineOptions)
    extends PrincessBasedBackend {

  private def translateCounterOffsets(
      products: Seq[RecordKeepingProduct],
      transitionToOffsets: TransitionToCounterOffsets
  ): TransitionToCounterOffsets =
    products.flatMap { product =>
      product.product.transitions.map { productTransition =>
        val mergedCounterIncrements =
          product
            .transitionOrigins(productTransition)
            .flatMap(transitionToOffsets(_))
            .toMap

        productTransition -> mergedCounterIncrements
      }
    }.toMap

  override def prepareSolver(
      p: SimpleAPI,
      instance: Instance
  ): Map[Counter, ConstantTerm] = {
    import ap.terfor.TerForConvenience._
    import p._

    // FIXME we need to start the timeout NOW because the product computation
    // itself can time out for large inputs.

    val products = trace("products") {
      instance.automata.map(terms => recordKeepingProduct(terms))
    }

    val productTransitionToOffsets =
      trace("product transition -> counter increments")(
        translateCounterOffsets(products, instance.transitionToOffsets)
      )

    val counterToSolverConstant =
      trace("Counter -> solver constant")(
        instance.counters
          .map(c => c -> p.createConstantRaw(c.name))
          .toMap
      )

    implicit val o = order // This needs to happen after the constant creation.

    // NOTE:  We need to iterate over only the live counters, because the
    // counters that were initially not mentioned by any automaton need to be
    // left without constraints and would otherwise be set to zero, despite
    // being unconstrained by the automata.
    val parikhConstraints: Seq[Conjunction] = products.map { product =>
      // This enforces the bridging clause: c  = SUM t : sigma(t) * increment(c, t)
      def transitionsIncrementRegisters(
          sigma: Map[Transition, ap.terfor.Term]
      ) =
        trace(s"binding clauses: counters are coherent:")(
          conj(instance.liveCounters.map { counter =>
            counterToSolverConstant(counter) === sum(
              product.product.transitions.map { transition =>
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

      product.product.parikhImage(
        transitionsIncrementRegisters(_),
        counterToSolverConstant.values.toSeq
      )
    }

    for (constraint <- instance.constraints) {
      p.addAssertion(
        trace("add constraint")(
          constraint toPrincess counterToSolverConstant
        )
      )
    }

    for (parikhConstraint <- parikhConstraints) {
      p.addAssertion(trace("parikhConstraint")(parikhConstraint))
    }

    counterToSolverConstant
  }

  private def recordKeepingProduct(
      terms: Seq[Automaton]
  ): RecordKeepingProduct = {

    assert(
      !terms.isEmpty,
      "Tried to compute a product of no automata: this is an edge case that should have been handled earlier in the process!"
    )

    var productSoFar: Automaton = terms.head
    // Product transition -> term transitions
    var transitionOrigins = productSoFar.transitions.map(t => t -> Seq(t)).toMap

    for (term <- terms.tail) {
      val newProduct = productSoFar productWithSources term
      productSoFar = newProduct.product
                ap.util.Timeout.check


      // Right origin is the originating transition in term, but Left origin
      // comes from partial product and needs to be resolved into its original
      // origin transitions. This is all a flatMap of sorts.
      transitionOrigins = productSoFar.transitions.map { productTransition =>
        val (partialProductOrigins, rightOrigin) =
          newProduct.originOfTransition(productTransition)

        val originatingTransitions = rightOrigin +: transitionOrigins(
          partialProductOrigins
        )

        productTransition -> originatingTransitions
      }.toMap
    }
    RecordKeepingProduct(transitionOrigins, productSoFar)
  }
}
