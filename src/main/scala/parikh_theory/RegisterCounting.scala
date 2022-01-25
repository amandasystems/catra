package uuverifiers.parikh_theory
import ap.theories.TheoryRegistry
import AutomataTypes.Transition
import ap.terfor.TerForConvenience.{l => toLinearCombination}

class RegisterCounting[C](
    counters: Seq[C],
    automata: Seq[Automaton],
    counterIncrements: Map[Transition, Map[C, Int]]
) extends ParikhTheory {
  override val auts = automata.toIndexedSeq
  override val monoidDimension = counters.length
  override def toMonoid(t: Transition) = {
    counters
      .map(
        c => counterIncrements(t).get(c).map(toLinearCombination)
      )
      .toSeq
  }

  TheoryRegistry register this

}
