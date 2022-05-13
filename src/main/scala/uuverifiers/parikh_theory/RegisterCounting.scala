package uuverifiers.parikh_theory
import ap.theories.TheoryRegistry
import uuverifiers.common.Automaton
import uuverifiers.common.AutomataTypes.Transition
import ap.terfor.TerForConvenience.{l => toLinearCombination}
import ap.proof.theoryPlugins.Plugin

class RegisterCounting[C](
    counters: Seq[C],
    automata: Seq[Automaton],
    counterIncrements: Map[Transition, Map[C, Int]],
    actionHooks: Seq[(Context, String, Seq[Plugin.Action]) => Unit] = Seq()
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

  override def actionHooks() = super.actionHooks() ++ actionHooks

  TheoryRegistry register this

}
