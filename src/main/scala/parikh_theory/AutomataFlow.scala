package uuverifiers.parikh_theory
import ap.parser.{IVariable, IFormula, IExpression}
import ap.terfor.{Formula, TermOrder}
import ap.terfor.linearcombination.LinearCombination
import ap.basetypes.IdealInt
import ap.basetypes.IdealInt.{ONE, ZERO, MINUS_ONE}
import ap.terfor.TerForConvenience._
import EdgeWrapper._

/**
 *  A class to generate flow-balancing constraints for an automaton, modulo an
 *  arbitrary mapping for edges.
 */
class AutomataFlow[A <: Automaton](private val aut: A)(
    implicit order: TermOrder
) extends Tracing {

  // From Label To
  private type Transition = (aut.State, aut.Label, aut.State)

  private def allNonnegative(vars: Seq[IVariable]) = conj(vars.map(_ >= 0))

  // TODO fold this into asManyIncomingAsOutgoing; it's short, single-use, and
  // only makes sense in that context.
  private def asStateFlowSum(
      stateTerms: Seq[(aut.State, (IdealInt, LinearCombination))]
  ) = {
    val (state, _) = stateTerms.head
    val isInitial = if (state == aut.initialState) ONE else ZERO
    (state, sum(stateTerms.unzip._2 ++ List((ONE, isInitial))))
  }

  /**
    * Compute the balancing constraints for the state flow stating that for each
    * state there are at least as many incoming and outgoing connections, as
    * defined by the mapping from transition to variable.
    */
  private def asManyIncomingAsOutgoing(
      transitionAndVar: Seq[(Transition, LinearCombination)]
  ): Formula = {

    trace("Flow equations") {
      conj(
        transitionAndVar
          .filter(!_._1.isSelfEdge)
          .flatMap {
            case ((from, _, to), transitionVar) =>
              List(
                (to, (ONE, transitionVar)),
                (from, (MINUS_ONE, transitionVar))
              )
          }
          .to
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

  def flowEquations(
      transitionTerms: Seq[IVariable],
      monoidVars: Seq[IVariable],
      toMonoid: Transition => Seq[LinearCombination]
  ): IFormula = {
    val transitionAndVar = aut.transitions.zip(transitionTerms.iterator)

    IExpression.and(
      Seq(
        allNonnegative(transitionTerms),
        allNonnegative(monoidVars),
        asManyIncomingAsOutgoing(transitionAndVar),
        monoidValuesReachable(monoidVars, transitionAndVar, toMonoid)
      ),
      order
    )
  }
}

object AutomataFlow {
  def apply[A <: Automaton](a: A)(implicit order: TermOrder) =
    new AutomataFlow(a)(order: TermOrder)
}
