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
  def toMonoid(a: (Any, Any, Any)): Seq[LinearCombination]

  /**
   *  This value represents the dimensionality of the sequence returned by
   * `toMonoid`.
    **/
  val monoidDimension: Int

  lazy val aut = auts(0) // lazy because of early init
  lazy private val autGraph = aut.toGraph // lazy because of aut
  // lazy private val cycles = trace("cycles")(autGraph.simpleCycles) // lazy because of aut

  // FIXME: total deterministisk ordning på edges!
  // lazy because it depends on aut
  lazy private val monoidMapPredicate =
    new Predicate(s"MonoidMap_${aut.hashCode}", monoidDimension + 1)

  private val transitionMaskPredicate =
    new Predicate(s"TransitionMask_${this.hashCode}", 4)

  override lazy val predicates =
    Seq(monoidMapPredicate, transitionMaskPredicate)

  def plugin: Option[Plugin] =
    Some(
      new ConnectednessPropagator(
        aut,
        monoidMapPredicate,
        transitionMaskPredicate,
        new TransitionMaskExtractor(transitionMaskPredicate),
        this
      )
    )

  /**
   * Generate a quantified formula that is satisfiable iff the provided
   * monoid values are possible by any legal path through the automaton.
   */
  def allowsMonoidValues(
      monoidValues: Seq[Term]
  )(implicit order: TermOrder): Formula = trace("allowsMonoidValues") {
    assert(monoidValues.length == this.monoidDimension)

    // FIXME adjust the threshold!
    // if (aut.states.size <= 10 || aut.transitions.size <= 10) {
    //   return (new PresburgerParikhImage(aut))
    //     .parikhImage(monoidValues, toMonoid _)
    // }

    val transitionTerms = autGraph.edges().indices.map(v).toIndexedSeq
    val instanceTerm = l(v(transitionTerms.size))
    val nrNewTerms = transitionTerms.size + 1

    // need to prevent variable capture by the quantifiers added below
    val shiftAwayFromQuantifiers =
      VariableShiftSubst.upShifter[Term](nrNewTerms, order)
    val shiftedMonoidValues = (monoidValues map shiftAwayFromQuantifiers) map (l _)

    val transitionMaskInstances =
      transitionTerms.zipWithIndex
        .map {
          case (t, i) =>
            transitionMaskPredicate(Seq(instanceTerm, l(0), l(i), l(t)))
        }

    // TODO evaluate whether this pays off!
    val predicateInstances =
      if (autGraph.simpleCycles().isEmpty) Seq()
      else
        monoidMapPredicate(instanceTerm +: shiftedMonoidValues) +: transitionMaskInstances

    val allEquations = exists(
      nrNewTerms,
      conj(
        AutomataFlow(aut).flowEquations(
          transitionTerms.map(l _).toSeq,
          monoidValues.map(l _).toSeq,
          toMonoid _
        ) +: predicateInstances
      )
    )

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
