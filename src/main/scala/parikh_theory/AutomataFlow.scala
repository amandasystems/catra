package uuverifiers.parikh_theory
import ap.terfor.{Formula, TermOrder, Term}
import ap.terfor.conjunctions.{Conjunction}
import ap.terfor.arithconj.ArithConj
import ap.terfor.linearcombination.LinearCombination
import ap.basetypes.IdealInt
import ap.basetypes.IdealInt.{ONE, ZERO, MINUS_ONE}
import EdgeWrapper._
import ap.terfor.TerForConvenience._

/**
 *  A class to generate flow-balancing constraints for an automaton, modulo an
 *  arbitrary mapping for edges.
 */
class AutomataFlow[A <: Automaton](private val aut: A)(
    implicit order: TermOrder
) extends Tracing {

  // From Label To
  private type Transition = (aut.State, aut.Label, aut.State)

  private def allNonnegative(vars: Seq[Term]) = conj(vars.map(_ >= 0))

  // TODO fold this into asManyIncomingAsOutgoing; it's short, single-use, and
  // only makes sense in that context.
  private def asStateFlowSum(
      stateTerms: Seq[(aut.State, (IdealInt, LinearCombination))]
  ) = {
    val (state, _) = stateTerms.head
    val initialFlow = l(if (state == aut.initialState) ONE else ZERO)
    (state, sum(stateTerms.unzip._2 ++ List((ONE, initialFlow))))
  }

  /**
   * Compute the balancing constraints for the state flow stating that for each
   * state there are at least as many incoming and outgoing connections, as
   * defined by the mapping from transition to variable.
   */
  private def asManyIncomingAsOutgoing(
      transitionAndVar: Seq[(Transition, LinearCombination)]
  ): ArithConj = {
    trace("Flow equations") {
      arithConj(
        transitionAndVar
          .filter(!_._1.isSelfEdge())
          .flatMap {
            case ((from, _, to), transitionVar) =>
              List(
                (to, (ONE, transitionVar)),
                (from, (MINUS_ONE, transitionVar))
              )
          }
          .groupBy(_._1)
          .values
          .map(asStateFlowSum)
          .map {
            case (state, flowSum) =>
              if (aut isAccept state) flowSum >= 0 else flowSum === 0
          }
      )
    }
  }

  /**
   *  This expresses the mapping between the monoid values and the transition
   *  variables. It is the y = Sum t : transitions tVar(t) * h(t), for both
   *  the h-values and y vectors.
   *
   *  TODO: How do we express that this multiplication happens on the
   *  monoid's multiplication?
   */
  private def monoidValuesReachable(
      monoidVars: Seq[LinearCombination],
      transitionAndVar: Seq[(Transition, LinearCombination)],
      toMonoid: Transition => Seq[LinearCombination]
  ): Formula = {
    trace("Monoid equations") {
      // This is just a starting vector of the same dimension as the monoid
      // values.
      val startVectorSum: Seq[LinearCombination] =
        Seq.fill(monoidVars.length)(LinearCombination(IdealInt.ZERO))
      conj(
        transitionAndVar
          .foldLeft(startVectorSum) {
            case (sums, (t, tVar)) =>
              toMonoid(t)
                .zip(sums)
                .map { case (monoidVal, sum) => sum + tVar * monoidVal }
          }
          .zip(monoidVars)
          .map { case (rVar, termSum) => rVar === termSum }
      )
    }
  }

  // TODO implement an IFormula version of this as well
  // FIXME the type casts here are really ugly
  def flowEquations(
      transitionAndVar: IndexedSeq[((Any, Any, Any), LinearCombination)],
      monoidVars: Seq[LinearCombination],
      toMonoid: Transition => Seq[LinearCombination]
  ): Conjunction = {
    trace("flowEquations")(
      conj(
        allNonnegative(transitionAndVar.unzip._2),
        allNonnegative(monoidVars),
        asManyIncomingAsOutgoing(
          transitionAndVar
            .asInstanceOf[IndexedSeq[(Transition, LinearCombination)]]
        ),
        monoidValuesReachable(
          monoidVars,
          transitionAndVar
            .asInstanceOf[IndexedSeq[(Transition, LinearCombination)]],
          toMonoid
        )
      )
    )
  }
}

object AutomataFlow {
  def apply[A <: Automaton](a: A)(implicit order: TermOrder) =
    new AutomataFlow(a)(order)
}
