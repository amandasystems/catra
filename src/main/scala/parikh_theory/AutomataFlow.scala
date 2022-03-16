package uuverifiers.parikh_theory
import ap.terfor.{Formula, TermOrder, Term}
import ap.terfor.conjunctions.{Conjunction}
import ap.terfor.arithconj.ArithConj
import ap.terfor.linearcombination.LinearCombination
import ap.basetypes.IdealInt
import ap.basetypes.IdealInt.{ONE, ZERO, MINUS_ONE}
import uuverifiers.common.EdgeWrapper._
import ap.terfor.TerForConvenience._
import uuverifiers.common.AutomataTypes._
import uuverifiers.common.{Tracing, Automaton}

/**
 *  A class to generate flow-balancing constraints for an automaton, modulo an
 *  arbitrary mapping for edges.
 */
class AutomataFlow(private val aut: Automaton)(
    implicit order: TermOrder
) extends Tracing {

  private def allNonnegative(vars: Seq[Term]) = conj(vars.map(_ >= 0))

  // TODO fold this into asManyIncomingAsOutgoing; it's short, single-use, and
  // only makes sense in that context.
  private def asStateFlowSum(
      stateTerms: Seq[(State, (IdealInt, LinearCombination))]
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
  def monoidValuesReachable(
      monoidVars: Seq[LinearCombination],
      transitionAndVar: IndexedSeq[(Transition, LinearCombination)],
      toMonoid: (Transition) => Seq[Option[LinearCombination]]
  ): Formula = {
    trace("Monoid equations") {
      // This is just a starting vector of the same dimension as the monoid
      // values. We start with no constraints, represented by None.
      val startMonoidIncrements: Seq[Option[LinearCombination]] =
        Seq.fill(monoidVars.length)(None)

      // The right-hand side of the equation of the individual monoid values, or
      // None if there isn't one.
      val monoidIncrements = transitionAndVar.foldLeft(startMonoidIncrements) {
        case (rhsEs, (t, tVar)) =>
          toMonoid(t).zip(rhsEs).map {
            case (None, counterRhs) => counterRhs
            case (Some(counterOffset), Some(counterRhs)) =>
              Some(counterRhs + tVar * counterOffset)
            case (Some(counterOffset), None) => Some(tVar * counterOffset)
          }
      }

      val transitionsConsistentWithMonoidValues =
        monoidIncrements.zip(monoidVars).map {
          case (Some(counterIncrements), counterVar) =>
            counterVar === counterIncrements
          // This nonsense is here to make it very clear that we are imposing no
          // constraints in this case. These no-op clauses impose an unnecessary
          // overhead, but it is probably not a problem.
          case (None, _) => Conjunction.TRUE
        }

      conj(
        conj(transitionsConsistentWithMonoidValues),
        allNonnegative(monoidVars)
      )
    }
  }

  // TODO implement an IFormula version of this as well
  def flowEquations(
      transitionAndVar: IndexedSeq[(Transition, LinearCombination)]
  ): Conjunction = {
    trace("flowEquations")(
      conj(
        allNonnegative(transitionAndVar.unzip._2),
        asManyIncomingAsOutgoing(transitionAndVar)
      )
    )
  }
}

object AutomataFlow {
  def apply(a: Automaton)(implicit order: TermOrder) =
    new AutomataFlow(a)(order)
}
