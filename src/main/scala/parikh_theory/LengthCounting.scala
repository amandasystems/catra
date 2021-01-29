package uuverifiers.parikh_theory
import ap.terfor.linearcombination.LinearCombination
import ap.basetypes.IdealInt
import ap.theories.TheoryRegistry

trait LengthCounting[A <: Automaton] extends ParikhTheory[A] {
  override def toMonoid(_t: Any) =
    Seq(LinearCombination(IdealInt.ONE))

  override val monoidDimension = 1
}

object LengthCounting {
  def apply[A <: Automaton](_auts: IndexedSeq[A]) =
    new ParikhTheory[A] with LengthCounting[A] {
      override val auts = _auts
      TheoryRegistry register this
    }
}
