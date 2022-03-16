package uuverifiers.parikh_theory

import ap.parser._
import ap.proof.goal.Goal
import ap.proof.theoryPlugins.{Plugin, TheoryProcedure}
import ap.terfor.preds.Atom
import ap.terfor.conjunctions.Conjunction
import ap.terfor.{TermOrder, Formula}
import ap.theories._
import ap.terfor.conjunctions.ReduceWithConjunction
import uuverifiers.common.Tracing

trait NoFunctions {
  val functionPredicateMapping
      : Seq[(ap.parser.IFunction, ap.parser.IExpression.Predicate)] = List()
  val functionalPredicates: Set[ap.parser.IExpression.Predicate] = Set()
  val functions: Seq[ap.parser.IFunction] = List()
  val predicateMatchConfig: ap.Signature.PredicateMatchConfig = Map()
  val triggerRelevantFunctions: Set[ap.parser.IFunction] = Set()
}

trait NoAxioms {
  val axioms: Formula = Conjunction.TRUE
  val totalityAxioms: ap.terfor.Formula = Conjunction.TRUE
}

trait Complete extends Theory {
  override def isSoundForSat(
      theories: Seq[Theory],
      config: Theory.SatSoundnessConfig.Value
  ): Boolean =
    Set(
      Theory.SatSoundnessConfig.Elementary,
      Theory.SatSoundnessConfig.Existential
    ) contains config
}

trait NoAxiomGeneration {
  /* We have to pretend to be using the argument to shut up the compiler
     warnings, and this is a cheap way of doing so. */
  def generateAxioms(goal: Goal) = goal match { case _ => None }
}

/** Provide a function to handle a predicate, automatically become a theory
 procedure handling the first instance of that predicate under the assumption
 that instances will be handled and eliminated one by one.
 */
trait PredicateHandlingProcedure extends TheoryProcedure with Tracing {
  val procedurePredicate: IExpression.Predicate
  def handlePredicateInstance(goal: Goal)(
      predicateAtom: Atom
  ): Seq[Plugin.Action]

  override def handleGoal(goal: Goal): Seq[Plugin.Action] =
    try {
      goal.facts.predConj
        .positiveLitsWithPred(procedurePredicate)
        .take(1) // Why can't we do all of them!?
        .flatMap(handlePredicateInstance(goal))
    } catch {
      case e: Throwable => logException(e); throw e
    }
}

/**
 * A helper to generate fresh variables though interior mutability.
  **/
class FreshVariables(private var nextVarIndex: Integer)(
    implicit order: TermOrder
) extends Tracing {
  import ap.terfor.TerForConvenience._
  def nextVariable() = {
    val thisVar = v(nextVarIndex)
    nextVarIndex += 1
    l(thisVar)
  }

  def variableCount() = nextVarIndex

  def exists(conjunction: Conjunction) = ap.terfor.TerForConvenience.exists(
    variableCount(),
    conjunction
  )

}

object VariousHelpers extends Tracing {
  def simplifyUnlessTimeout(
      order: TermOrder,
      formula: Conjunction
  ): Conjunction =
    try {
      ReduceWithConjunction(Conjunction.TRUE, order)(formula)
    } catch {
      case ap.util.Timeout(_) => trace("Timeout while simplifying")(formula)
    }
}
