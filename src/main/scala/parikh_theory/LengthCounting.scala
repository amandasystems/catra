package uuverifiers.parikh_theory
import ap.terfor.linearcombination.LinearCombination
import ap.basetypes.IdealInt
import ap.theories.TheoryRegistry

trait LengthCounting[A <: Automaton] extends ParikhTheory[A] {
  override val toMonoid = _ => Seq(LinearCombination(IdealInt.ONE))
}

object LengthCounting {
  def apply[A <: Automaton](_aut: A) =
    new ParikhTheory[A] with LengthCounting[A] {
      override val aut = _aut
      TheoryRegistry register this
    }
}
