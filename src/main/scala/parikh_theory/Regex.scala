package uuverifiers.parikh_theory
import SymbolicLabelConversions._

sealed abstract class Regex extends Product with Serializable {
  def toAutomaton(): Automaton
  def after(that: Regex) =
    Regex.Serial(that, this) // TODO for Word, these are trival
  def before(that: Regex) =
    Regex.Serial(this, that) // TODO for Word, these are trival
  def or(that: Regex) = Regex.Parallel(this, that)
  def onceOrMore() = Regex.RepeatInfinitely(this)
}

object Regex {
  def apply(): Regex = Word("")
  def apply(regex: String): Regex = Word(regex)

  final case class Word(w: String) extends Regex {
    def toAutomaton() = {
      val builder = AutomatonBuilder()
      builder
        .addStates(0 to w.length)
        .setInitial(0)
        .setAccepting(w.length)

      if (w.nonEmpty) {
        w.zipWithIndex.foreach {
          case (ch, thisState) =>
            builder.addTransition(thisState, ch, thisState + 1)
        }
      }
      builder.getAutomaton()
    }

  }
  final case class Serial(first: Regex, second: Regex) extends Regex {
    def toAutomaton() = first.toAutomaton() ++ second.toAutomaton()
  }

  final case class Parallel(left: Regex, right: Regex) extends Regex {
    def toAutomaton() = left.toAutomaton() ||| right.toAutomaton()
  }
  final case class RepeatInfinitely(toRepeat: Regex) extends Regex {
    def toAutomaton() = {
      val aut = toRepeat.toAutomaton()
      val builder = AutomatonBuilder(aut)

      aut.states.filter(aut.isAccept).foreach { s =>
        // out-edges of accepting states inherit all out-edges of the initial state
        aut
          .transitionsFrom(aut.initialState)
          .foreach(t => builder.addTransitionTuple(t.copy(_1 = s)))
      }

      builder.getAutomaton()
    }

  }
}
