package uuverifiers.parikh_theory
import ap.theories.TheoryRegistry
import uuverifiers.common.{Automaton, Counting, Transition}
import ap.terfor.TerForConvenience.{l => toLinearCombination}
import ap.proof.theoryPlugins.Plugin
import ap.terfor.conjunctions.Conjunction
import ap.terfor.{Term, TermOrder}
import ap.terfor.linearcombination.LinearCombination
import uuverifiers.catra.Counter

class RegisterCounting(
    automata: Seq[Automaton],
    actionHooks: Seq[(Context, String, Seq[Plugin.Action]) => Unit] = Seq()
) extends ParikhTheory {
  private val counters =
    automata
      .flatMap(_.counters())
      .toSet
      .toIndexedSeq
      .sortBy((c: Counter) => c.name)
  override val auts: IndexedSeq[Automaton] =
    automata.toIndexedSeq
  override val monoidDimension: Int = counters.size
  override def toMonoid(t: Transition): Seq[Option[LinearCombination]] = {
    // FIXME do away with this cast
    val tCast = t.asInstanceOf[Counting]
    counters.map(c => (tCast increments c).map(toLinearCombination))
  }

  def allowsCounterValues(counterToTerm: Map[Counter, Term])(
      implicit order: TermOrder
  ): Conjunction = allowsMonoidValues(counters.map(counterToTerm))

  override def actionHooks()
      : Seq[(Context, String, Seq[Plugin.Action]) => Unit] =
    super.actionHooks() ++ actionHooks

  TheoryRegistry register this

}
