package uuverifiers.parikh_theory

import ap.proof.goal.Goal
import ap.terfor.linearcombination.LinearCombination
import ap.parser.IExpression.Predicate
import ap.terfor.preds.Atom

class TransitionMaskExtractor(private val theoryInstance: ParikhTheory)
    extends Tracing {
  import TransitionSelected.{Present, Absent, Unknown}
  import theoryInstance._

  // FIXME make this a nice wrapper class instead
  def instanceTerm(transitionMask: Atom) =
    transitionMaskToTuple(transitionMask)._1
  def transitionNr(transitionMask: Atom) =
    transitionMaskToTuple(transitionMask)._3
  def transitionTerm(transitionMask: Atom) =
    transitionMaskToTuple(transitionMask)._4

  def autId(connectedOrTransitionMask: Atom): Int =
    connectedOrTransitionMask.pred match {
      case `transitionMaskPredicate` =>
        transitionMaskToTuple(connectedOrTransitionMask)._2
      case `connectedPredicate` | `unusedPredicate` =>
        connectedOrTransitionMask(1).constant.intValue
      case unknown =>
        throw new IllegalArgumentException(s"Unknown predicate ${unknown}")
    }

  /**
   * Take a TransitionMask predicate, and extract its indices.
   */
  def transitionMaskToTuple(atom: Atom) = {
    assert(atom.pred == transitionMaskPredicate)
    val instanceIdTerm :+ productOffset :+ tIdxTerm :+ tVal =
      atom.toSeq: @unchecked
    (
      instanceIdTerm(0),
      productOffset.constant.intValue,
      tIdxTerm.constant.intValue,
      tVal
    )
  }

  // NOTE this is based on the fact that the first term is always the instance
  // in all predicates. There's no typesafe way to express this.
  def goalAssociatedPredicateInstances(goal: Goal, instance: LinearCombination)(
      predicate: Predicate
  ) =
    goal.facts.predConj
      .positiveLitsWithPred(predicate)
      .filter(_(0) == instance)

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
    trace(s"TransitionMasks for ${instance} in goal age ${goal.age}") {
      val (productOffsets, transitionTerms) =
        goalAssociatedPredicateInstances(goal, instance)(
          transitionMaskPredicate
        ).map(transitionMaskToTuple)
          .sortBy(_._3)
          .unzip(x => (x._2, x._4))

      // NOTE we need this check in some instances, notably when the automaton
      // was cycle-free and thus needed no transition terms. In future versions,
      // this should lead to the connectedness propagator not being loaded at
      // all, and then the check for isEmpty should not be needed.
      (transitionTerms, if (productOffsets.isEmpty) 0 else productOffsets.max)

    }

  def transitionStatusFromTerm(
      goal: Goal,
      term: LinearCombination
  ): TransitionSelected = {
    lazy val lowerBound = goal.reduceWithFacts.lowerBound(term)
    lazy val upperBound = goal.reduceWithFacts.upperBound(term)

    if (lowerBound.exists(_ > 0)) Present
    else if (upperBound.exists(_ <= 0)) Absent
    else Unknown
  }

  def termMeansDefinitelyAbsent(
      goal: Goal,
      term: LinearCombination
  ): Boolean = {
    term match {
      case LinearCombination.Constant(x) => x <= 0
      case _                             => goal.reduceWithFacts.upperBound(term).exists(_ <= 0)
    }

  }

  def termMeansPossiblyAbsent(
      goal: Goal,
      term: LinearCombination
  ): Boolean = {
    term match {
      case LinearCombination.Constant(x) => x <= 0
      case _                             => !goal.reduceWithFacts.lowerBound(term).exists(_ > 0)
    }

  }
}
