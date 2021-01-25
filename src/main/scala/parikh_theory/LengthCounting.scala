package uuverifiers.parikh_theory
import ap.terfor.linearcombination.LinearCombination
import ap.basetypes.IdealInt
import ap.theories.TheoryRegistry

trait LengthCounting[A <: Automaton] extends ParikhTheory[A] {
  override def toMonoid(_t: aut.Transition) =
    Seq(LinearCombination(IdealInt.ONE))
  
  override val monoidDimension = 1
}

object LengthCounting {
  def apply[A <: Automaton](_aut: A) =
    new ParikhTheory[A] with LengthCounting[A] {
      override val aut = _aut
      TheoryRegistry register this
    }
}
