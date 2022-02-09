package uuverifiers.parikh_theory

import ap.proof.theoryPlugins.Plugin
import ap.terfor.conjunctions.{Conjunction, ReduceWithConjunction}
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.{TermOrder, Formula, Term}
import ap.terfor.substitutions.{VariableShiftSubst}
import ap.theories._
import ap.parser.IExpression.Predicate
import ap.terfor.TerForConvenience._
import AutomataTypes._

// TODO write a LengthCounting mixin which interns one term for length and
// yields that for each transition
// TODO work through terminology. Why do we use "register values"?
// TODO use [M <: Monoid with Abelian, A <: Automaton]

/**
 * The Parikh Theory enforces Parikh Image membership modulo a morphism to a
 * commutative monoid. The most straightforward example is string length, with
 * an automaton representing the possible strings.
 *
 * NOTE: this is a theory factory, it never registers itself, that's on you, the
 * caller!
 *
 * WARNING! fields are lazy because of how initialisation works in scala (it's
 * Not Great.)
 */
trait ParikhTheory
    extends Theory
    with NoFunctions
    with NoAxioms
    with Tracing
    with Complete {
  val auts: IndexedSeq[Automaton]

  /**
   * This method provides the "modulo" aspect by performing the translation from
   * a transition (usually really the transition's label) to a commutative
   * monoid (M).
   *
   * Must always return something of length monoidDimension.
   *
   * For example length-counting would map all transitions representing a single
   * character (typically all transitions) to 1. Note: we use Option here to
   * differentiate "no opinion" from increments. In this sense, a toMonoid(t)(i) =
   * None means "taking transition t does not alter the value of variable i."
    **/
  def toMonoid(a: Transition): Seq[Option[LinearCombination]]

  /**
   *  This value represents the dimensionality of the sequence returned by
   * `toMonoid`.
    **/
  val monoidDimension: Int

  /** The prefix to use when dumping dot files for automata, etc.
   **/
  lazy val filePrefix: String = s"ParikhTheory_${this.hashCode}"

  // Lazy because early init would set the monoidDimension to 0
  // MonoidMap(s, m1, ..., mn): Instance s maps to monoid values m1...mn
  lazy val monoidMapPredicate =
    new Predicate(s"MonoidMap_${this.hashCode}", monoidDimension + 1)

  // TransitionMask(s, a, t, x): Automaton a of instance s maps transition t to term x
  val transitionMaskPredicate =
    new Predicate(s"TransitionMask_${this.hashCode}", 4)

  // Connected(s, n): Automaton n of instance s is connected
  val connectedPredicate =
    new Predicate(s"Connected_${this.hashCode}", 2)

  // Unused(s, n): Automaton n of instance s is not yet used in a
  // product.
  val unusedPredicate =
    new Predicate(s"Unused_${this.hashCode}", 2)

  override lazy val predicates =
    Seq(
      monoidMapPredicate,
      transitionMaskPredicate,
      connectedPredicate,
      unusedPredicate
    )

  lazy val monoidMapPlugin = new MonoidMapPlugin(this)

  /**
   * A hook to do something whenever an action is taken. Typically used for
   * logging and debugging. The default is to do...nothing.
   */
  def actionHook(
      context: monoidMapPlugin.Context,
      action: String,
      actions: Seq[Plugin.Action]
  ): Unit = {}

  def plugin: Option[Plugin] = Some(monoidMapPlugin)

  // FIXME separate out the mapping to the monoid values
  /**
   * Generate the clauses for the i:th automaton. Introduces a number of new
   * terms. Returns the formula and new offset.
   */
  def automataClauses(
      automaton: Automaton,
      instanceTerm: LinearCombination,
      automataNr: Int,
      transitionAndTerms: IndexedSeq[(Transition, LinearCombination)]
  )(implicit order: TermOrder): Seq[Formula] = {
    val transitionMaskInstances =
      transitionAndTerms.unzip._2.zipWithIndex
        .map {
          case (transitionTerm, transitionIdx) =>
            transitionMaskPredicate(
              Seq(instanceTerm, l(automataNr), l(transitionIdx), transitionTerm)
            )
        }

    val isUnusedInProduct = unusedPredicate(Seq(instanceTerm, l(automataNr)))
    val isConnected = connectedPredicate(Seq(instanceTerm, l(automataNr)))
    val preservesFlow =
      AutomataFlow(automaton).flowEquations(transitionAndTerms)

    isUnusedInProduct +: isConnected +: preservesFlow +: transitionMaskInstances

  }

  /**
   * Generate a quantified formula that is satisfiable iff the provided
   * monoid values are possible by any legal path through the automaton.
   *  This will materialise:
   *  - the MonoidMap predicate for this instance
   *  - all TransitionMask predicates for the first automaton
   *  - the flow equations for the first automaton.
   */
  def allowsMonoidValues(
      monoidValues: Seq[Term]
  )(implicit order: TermOrder): Conjunction =
    trace(s"allowsMonoidValues(${monoidValues})") {
      assert(
        monoidValues.length == this.monoidDimension,
        s"got ${monoidValues.length} monoid values, monoid dimension is ${monoidDimension}"
      )

      trace(s"nr of automata: ${auts.size}")("")

      // TODO refactor this into a builder pattern for the exists clause?
      val varFactory = new FreshVariables(0)
      val instanceTerm = varFactory.nextVariable()

      val autTransitionTerms
          : IndexedSeq[IndexedSeq[(Transition, LinearCombination)]] =
        auts.map(
          _.transitions.map(t => (t, varFactory.nextVariable())).toIndexedSeq
        )

      // need to prevent variable capture by the quantifiers added below
      val shiftAwayFromQuantifiers =
        VariableShiftSubst.upShifter[Term](varFactory.variableCount(), order)
      val shiftedMonoidValues
          : Seq[LinearCombination] = (monoidValues map shiftAwayFromQuantifiers) map (l _)

      val clauses =
        auts.zipWithIndex.flatMap {
          case (a, i) =>
            automataClauses(
              a,
              instanceTerm,
              i,
              autTransitionTerms(i)
            ) :+ AutomataFlow(a).monoidValuesReachable(
              shiftedMonoidValues,
              autTransitionTerms(i),
              toMonoid
            )
        }

      trace(s"created ${varFactory.variableCount()} terms in")(clauses)

      val thisMonoidMapInstance =
        monoidMapPredicate(instanceTerm +: shiftedMonoidValues)

      val allEquations = trace("allEquations before simplification") {
        varFactory.exists(conj(thisMonoidMapInstance +: clauses))
      }

      val simplifiedEquations =
        ReduceWithConjunction(Conjunction.TRUE, order)(allEquations)

      // TODO check if the flow equations have just one solution, in that case just return that.
      // Use  simplifiedEquations.quans: check if empty, and WHAT MORE???
      // TODO also add analysis for simple automata, or perhaps do that earlier?
      simplifiedEquations
    }

  def dumpGraphs() = monoidMapPlugin.dumpGraphs()

}

// TODO turn this into a theory builder?
object ParikhTheory {
  def apply(_auts: IndexedSeq[Automaton])(
      _toMonoid: Transition => Seq[Option[LinearCombination]],
      _monoidDimension: Int
  ) = {
    new ParikhTheory {
      override val auts = _auts
      override def toMonoid(t: Transition) = _toMonoid(t)
      override val monoidDimension = _monoidDimension

      TheoryRegistry register this
    }
  }
}
