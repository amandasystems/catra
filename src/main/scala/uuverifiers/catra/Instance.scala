package uuverifiers.catra

import uuverifiers.common.Automaton

sealed case class Instance(
    counters: Seq[Counter],
    automataProducts: Seq[Seq[Automaton]],
    constraints: Seq[Formula]
) extends InputValidating {
  def validate(): ValidationResult = super.validate(this)
}
