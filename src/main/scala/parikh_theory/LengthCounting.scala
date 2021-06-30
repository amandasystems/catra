package uuverifiers.parikh_theory
import ap.terfor.linearcombination.LinearCombination
import ap.basetypes.IdealInt
import ap.theories.TheoryRegistry
import AutomataTypes.Transition

trait LengthCounting extends ParikhTheory {
  override def toMonoid(_t: Transition) =
    Seq(LinearCombination(IdealInt.ONE))

  override val monoidDimension = 1
}

object LengthCounting {
  def apply(_auts: IndexedSeq[Automaton]) =
    new ParikhTheory with LengthCounting {
      override val auts = _auts
      TheoryRegistry register this
    }
}
