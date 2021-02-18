package uuverifiers.parikh_theory

import ap.proof.goal.Goal
import ap.terfor.linearcombination.LinearCombination
import ap.parser.IExpression.Predicate
import ap.terfor.preds.Atom

class TransitionMaskExtractor(private val transitionMaskPredicate: Predicate)
    extends Tracing {
  import TransitionSelected.{Present, Absent, Unknown}

  /**
   * Take a TransitionMask predicate, and extract its indices.
   */
  private def transitionMaskToTuple(atom: Atom) = {
    val instanceIdTerm :+ _ :+ tIdxTerm :+ tVal = atom.toSeq
    // TODO in the future, we will need all indices!
    (instanceIdTerm(0), tIdxTerm.constant.intValue, tVal)
  }

  def goalTransitionTerms(
      goal: Goal,
      instance: LinearCombination
  ) =
    trace(s"TransitionMasks for ${instance} in ${goal}") {
      goal.facts.predConj
        .positiveLitsWithPred(transitionMaskPredicate)
        .map(transitionMaskToTuple)
        .filter { case (i, _, _) => i == instance }
        .sortBy(_._2)
        .map(_._3)
    }

  def transitionStatusFromTerm(
      goal: Goal,
      term: LinearCombination
  ): TransitionSelected = trace(s"selection status for ${term} is ") {
    lazy val lowerBound = goal.reduceWithFacts.lowerBound(term)
    lazy val upperBound = goal.reduceWithFacts.upperBound(term)

    if (lowerBound.exists(_ > 0)) Present
    else if (upperBound.exists(_ <= 0)) Absent
    else Unknown
  }

  def termMeansDefinitelyAbsent(
      goal: Goal,
      term: LinearCombination
  ): Boolean = trace(s"termMeansDefinitelyAbsent(${term})") {
    term match {
      case LinearCombination.Constant(x) => x <= 0
      case _                             => goal.reduceWithFacts.upperBound(term).exists(_ <= 0)
    }

  }
}
