package uuverifiers.parikh_theory
import AutomataTypes.Transition
import SymbolicLabel.NoChar

object LengthCounting {
  private val lengthSymbol = 'l'
  private val incrementLength = Map(lengthSymbol -> 1)
  private val noOp = Map(lengthSymbol -> 0)

  private def transitionToIncrement(t: Transition) = t match {
    case t @ (_, NoChar, _) => t -> noOp
    case _                  => t -> incrementLength
  }

  // Get a fresh state ID that was not used in either of these automata
  private def freshState(auts: Seq[Automaton]) =
    auts.map(_.states.max).max + 1

  def apply(_auts: IndexedSeq[Automaton]) = {
    val auts = for (a <- _auts) yield {
      if (a.transitions.isEmpty && a.isAccept(a.initialState)) {
        // Special case: a accepts only the empty string. In order to set up the
        // input correctly, we need to make sure the length counter is mentioned
        // here, thereby constraining it to be 0. We do this by introducing an
        // epsilon transition that does not change the counter value.

        val newInitial = freshState(_auts)
        AutomatonBuilder()
          .addState(newInitial)
          .setAccepting(newInitial)
          .setInitial(newInitial)
          .addStates(a.states)
          .addTransition(newInitial, NoChar, a.initialState)
          .setAccepting(a.initialState)
          .getAutomaton()
      } else {
        a
      }
    }
    new RegisterCounting(
      counters = Seq(lengthSymbol),
      automata = auts,
      counterIncrements =
        auts.flatMap(a => a.transitions.map(transitionToIncrement)).toMap
    )
  }
}
