package uuverifiers.common
import SymbolicLabelConversions._
import scala.language.implicitConversions

sealed abstract class Regex extends Product with Serializable {
  def toAutomaton(): Automaton
  def precededBy(that: Regex) =
    Regex.Serial(that, this) // TODO for Word, these are trival
  def followedBy(that: Regex) =
    Regex.Serial(this, that) // TODO for Word, these are trival
  def or(that: Regex) = Regex.Parallel(this, that)
  def onceOrMore() = Regex.RepeatInfinitely(this)
}

object Regex {
  def apply(): Regex = Word("")
  def apply(regex: String): Regex = Word(regex)

  final case object AnyChar extends Regex {
    override def toAutomaton() = {
      val states = (0 to 1).map(IntState(_)).toIndexedSeq
      AutomatonBuilder()
        .addStates(states)
        .setInitial(states(0))
        .setAccepting(states(1))
        .addTransition(states(0), SymbolicLabel.AnyChar, states(1))
        .getAutomaton()
    }
  }

  final case class Word(w: String) extends Regex {
    override def toAutomaton() = {
      val builder = AutomatonBuilder()
      val states = (0 to w.length).map(IntState(_)).toIndexedSeq
      builder
        .addStates(states)
        .setInitial(states(0))
        .setAccepting(states.last)

      if (w.nonEmpty) {
        w.zipWithIndex.foreach {
          case (ch, thisState) =>
            builder.addTransition(states(thisState), ch, states(thisState + 1))
        }
      }
      builder.getAutomaton()
    }

  }
  final case class Serial(first: Regex, second: Regex) extends Regex {
    override def toAutomaton() = first.toAutomaton() ++ second.toAutomaton()
  }

  final case class Parallel(left: Regex, right: Regex) extends Regex {
    override def toAutomaton() = left.toAutomaton() ||| right.toAutomaton()
  }
  final case class RepeatInfinitely(toRepeat: Regex) extends Regex {
    override def toAutomaton() = {
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

object RegexImplicits {
  implicit def stringToWord(w: String): Regex = Regex(w)

}
