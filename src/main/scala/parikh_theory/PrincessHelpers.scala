package uuverifiers.parikh_theory

import ap.parser._
import ap.proof.goal.Goal
import ap.proof.theoryPlugins.{Plugin, TheoryProcedure}
import ap.terfor.preds.Atom
import ap.terfor.conjunctions.Conjunction
import ap.terfor.{TermOrder, Formula}
import ap.theories._
import scala.annotation.elidable
import scala.annotation.elidable.FINE

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

trait Tracing {
  @elidable(FINE)
  protected def logInfo(message: String) = System.err.println(message)

  protected def trace[T](message: String)(something: T): T = {
    logInfo(s"trace::${message}(${something})")

    something
  }
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
  def generateAxioms(_goal: Goal) = None
}

/** Provide a function to handle a predicate, automatically become a theory
 procedure handling the first instance of that predicate under the assumption
 that instances will be handled and eliminated one by one.
 */
trait PredicateHandlingProcedure extends TheoryProcedure {
  val procedurePredicate: IExpression.Predicate
  def handlePredicateInstance(goal: Goal)(
      predicateAtom: Atom
  ): Seq[Plugin.Action]

  override def handleGoal(goal: Goal): Seq[Plugin.Action] =
    goal.facts.predConj
      .positiveLitsWithPred(procedurePredicate)
      .take(1)
      .flatMap(handlePredicateInstance(goal))
}

/**
 * A helper to generate fresh variables though interior mutability.
  **/
class FreshVariables(private var nextVarIndex: Integer)(
    implicit order: TermOrder
) extends Tracing {
  import ap.terfor.TerForConvenience._
  def nextVariable() = trace("Fresh variable") {
    val thisVar = v(nextVarIndex)
    nextVarIndex += 1
    l(thisVar)
  }

  def variableCount() = nextVarIndex
}
