package uuverifiers.parikh_theory
import ap.terfor.linearcombination.LinearCombination
import ap.basetypes.IdealInt
import ap.theories.TheoryRegistry

trait LengthCounting[S, L, A <: Automaton[S, L]] extends ParikhTheory[S, L, A] {
  override def toMonoid(_t: Any) =
    Seq(LinearCombination(IdealInt.ONE))

  override val monoidDimension = 1
}

object LengthCounting {
  def apply[S, L, A <: Automaton[S, L]](_auts: IndexedSeq[A]) =
    new ParikhTheory[S, L, A] with LengthCounting[S, L, A] {
      override val auts = _auts
      TheoryRegistry register this
    }
}
