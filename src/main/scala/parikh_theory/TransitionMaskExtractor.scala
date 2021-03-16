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
    val instanceIdTerm :+ productOffset :+ tIdxTerm :+ tVal = atom.toSeq
    // TODO in the future, we will need all indices!
    (
      instanceIdTerm(0),
      productOffset.constant.intValue,
      tIdxTerm.constant.intValue,
      tVal
    )
  }

  /**
   * Extract the transition terms out of a (proof) Goal, as long as it follows
   * a given instance. Returns a tuple of the transitions for the given
   * instance (ordered by transition index), and the maximum depth of product
   * materialisation encountered.
   *  TODO: should we just use a separate predicate to log materialisation depth?
   */
  def goalTransitionTerms(
      goal: Goal,
      instance: LinearCombination
  ) =
    trace(s"TransitionMasks for ${instance} in ${goal}") {
      val (productOffsets, transitionTerms) = goal.facts.predConj
        .positiveLitsWithPred(transitionMaskPredicate)
        .map(transitionMaskToTuple)
        .filter(_._1 == instance)
        .sortBy(_._3)
        .unzip(x => (x._2, x._4))

      (transitionTerms, productOffsets.max)

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
