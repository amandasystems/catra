package uuverifiers.parikh_theory

import ap.proof.theoryPlugins.Plugin
import ap.terfor.conjunctions.{Conjunction, ReduceWithConjunction}
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.{TermOrder, Formula, Term}
import ap.terfor.substitutions.{VariableShiftSubst}
import ap.theories._
import ap.parser.IExpression.Predicate
import ap.terfor.TerForConvenience._

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
trait ParikhTheory[A <: Automaton]
    extends Theory
    with NoFunctions
    with NoAxioms
    with Tracing
    with Complete {

  val auts: IndexedSeq[A]

  type Transition = (Any, Any, Any)

  /**
   * This method provides the "modulo" aspect by performing the translation
   * from a transition (usually really the transition's label) to a commutative
   * monoid (M).
   *
   * Must always return something of length monoidDimension.
   *
   * For example length-counting would map all transitions representing a
   * single character (typically all transitions) to 1.
   * NOTE: takes Any argument because Scala's type system isn't sophisticated
   * enough, or I am not sophisticated enough for it. 1-2 of those.
    **/
  def toMonoid(a: Transition): Seq[LinearCombination]

  /**
   *  This value represents the dimensionality of the sequence returned by
   * `toMonoid`.
    **/
  val monoidDimension: Int

  // lazy because it depends on auts
  lazy private val monoidMapPredicate =
    new Predicate(s"MonoidMap_${this.hashCode}", monoidDimension + 1)

  private val transitionMaskPredicate =
    new Predicate(s"TransitionMask_${this.hashCode}", 4)

  override lazy val predicates =
    Seq(monoidMapPredicate, transitionMaskPredicate)

  def plugin: Option[Plugin] =
    Some(
      new ConnectednessPropagator(
        auts,
        monoidMapPredicate,
        transitionMaskPredicate,
        new TransitionMaskExtractor(transitionMaskPredicate),
        this
      )
    )

  /**
   * Generate the clauses for the i:th automaton. Introduces a number of new
   * terms. Returns the formula and new offset.
   */
  private def automataClauses(
      instanceTerm: LinearCombination,
      automataNr: Int,
      transitionAndTerms: IndexedSeq[(Transition, LinearCombination)],
      monoidValues: Seq[Term]
  )(implicit order: TermOrder): Seq[Formula] = {
    val aut = auts(automataNr)
    val autGraph = aut.toGraph

    // FIXME adjust the threshold!
    // if (aut.states.size <= 10 || aut.transitions.size <= 10) {
    //   return (new PresburgerParikhImage(aut))
    //     .parikhImage(monoidValues, toMonoid _)
    // }

    val transitionMaskInstances =
      transitionAndTerms.unzip._2.zipWithIndex
        .map {
          case (transitionTerm, transitionIdx) =>
            transitionMaskPredicate(
              Seq(instanceTerm, l(automataNr), l(transitionIdx), transitionTerm)
            )
        }

    // TODO evaluate whether this pays off!
    val predicateInstances =
      if (autGraph.simpleCycles().isEmpty) Seq()
      else transitionMaskInstances

    AutomataFlow(aut).flowEquations(
      transitionAndTerms,
      monoidValues.map(l _).toSeq,
      toMonoid _
    ) +: predicateInstances

  }

  /**
   * Generate a quantified formula that is satisfiable iff the provided
   * monoid values are possible by any legal path through the automaton.
   */
  def allowsMonoidValues(
      monoidValues: Seq[Term]
  )(implicit order: TermOrder): Formula = trace("allowsMonoidValues") {
    assert(monoidValues.length == this.monoidDimension)

    trace(s"nr of automata: ${auts.size}")("")

    val varFactory = new FreshVariables(0)
    val instanceTerm = varFactory.nextVariable()

    val allTransitionTerms = this.auts.map { a =>
      a.transitions.map(t => (t, varFactory.nextVariable())).toIndexedSeq
    }.toIndexedSeq

    // need to prevent variable capture by the quantifiers added below
    val shiftAwayFromQuantifiers =
      VariableShiftSubst.upShifter[Term](varFactory.variableCount(), order)
    val shiftedMonoidValues
        : Seq[LinearCombination] = (monoidValues map shiftAwayFromQuantifiers) map (l _)

    val clauses = auts.zipWithIndex.flatMap {
      case (aut, autId) =>
        automataClauses(
          instanceTerm,
          autId,
          allTransitionTerms(autId),
          shiftedMonoidValues
        )
    }

    trace(s"created ${varFactory.variableCount()} terms in")(clauses)

    val thisMonoidMapInstance =
      monoidMapPredicate(instanceTerm +: shiftedMonoidValues)

    val allEquations = trace("allEquations before simplification") {
      exists(
        varFactory.variableCount(),
        conj(thisMonoidMapInstance +: clauses)
      )
    }

    val simplifiedEquations =
      ReduceWithConjunction(Conjunction.TRUE, order)(allEquations)

    // TODO check if the flow equations have just one solution, in that case just return that.
    // Use  simplifiedEquations.quans: check if empty, and WHAT MORE???
    // TODO also add analysis for simple automata, or perhaps do that earlier?
    simplifiedEquations
  }

}

// TODO turn this into a theory builder?
object ParikhTheory {
  def apply[A <: Automaton](_auts: IndexedSeq[A])(
      _toMonoid: Any => Seq[LinearCombination],
      _monoidDimension: Int
  ) = {
    new ParikhTheory[A] {
      override val auts: IndexedSeq[A] = _auts
      override def toMonoid(t: (Any, Any, Any)) = _toMonoid(t)
      override val monoidDimension = _monoidDimension

      TheoryRegistry register this
    }
  }
}
