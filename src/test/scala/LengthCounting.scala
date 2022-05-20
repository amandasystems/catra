import uuverifiers.catra.Counter
import uuverifiers.common.SymbolicLabel.NoChar
import uuverifiers.common._
import uuverifiers.parikh_theory.RegisterCounting

object LengthCounting {
  private val lengthSymbol = Counter("length")
  private val incrementLength = lengthSymbol incrementBy 1
  private val noOp = lengthSymbol incrementBy 0

  // Get a fresh state ID that was not used in either of these automata
  // FIXME get rid of this instance of asInstanceOf
  private def freshState(auts: Seq[Automaton]): IntState =
    auts.map(_.states.map(s => s.asInstanceOf[IntState]).max).max.successor()

  def apply(_auts: IndexedSeq[Automaton]): RegisterCounting = {
    val auts = {
      for (a <- _auts) yield {
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
            .addTransition(Counting(newInitial, NoChar, noOp, a.initialState))
            .setAccepting(a.initialState)
            .getAutomaton()
        } else {
          a
        }
      }
    }.map { a =>
      new Automaton {
        override def states: Iterable[State] = a.states
        override def transitionsFrom(from: State): Seq[Counting] = {
          a.transitionsFrom(from)
            .map {
              case t: Counting           => t
              case t: SymbolicTransition => t.withIncrements(incrementLength)
            }
        }
        override val initialState: State = a.initialState
        override def isAccept(s: State): Boolean = a.isAccept(s)
        override def counters(): Set[Counter] = Set(lengthSymbol)
      }
    }
    new RegisterCounting(automata = auts)
  }
}
