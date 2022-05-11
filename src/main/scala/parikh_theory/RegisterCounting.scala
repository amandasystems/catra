package uuverifiers.parikh_theory
import ap.theories.TheoryRegistry
import uuverifiers.common.Automaton
import uuverifiers.common.AutomataTypes.Transition
import ap.terfor.TerForConvenience.{l => toLinearCombination}

class RegisterCounting[C](
    counters: Seq[C],
    automata: Seq[Automaton],
    counterIncrements: Map[Transition, Map[C, Int]],
    actionHook: Option[
      (Context, String, Seq[ap.proof.theoryPlugins.Plugin.Action]) => Unit
    ] = None
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

  override def actionHooks() = actionHook match {
    case Some(hook) => super.actionHooks() appended hook
    case None => super.actionHooks()
  }

  TheoryRegistry register this

}
