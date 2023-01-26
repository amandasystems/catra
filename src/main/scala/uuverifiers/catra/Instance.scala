package uuverifiers.catra

import uuverifiers.common.Automaton

sealed case class Instance(
    counters: Seq[Counter],
    automataProducts: Seq[Seq[Automaton]],
    constraints: Seq[Formula]
) extends InputValidating {
  def validate(): ValidationResult = super.validate(this)

  override def toString: String = {
    val counterList = counters.map(_.toString).mkString(", ")
    val automataSection = automataProducts.map { product =>
      val automataStr = product.map(a => a.serialise()).mkString("\n\n")
      s"synchronised {\n$automataStr\n};\n"
    }
    val constraintSection =
      constraints.map(c => s"constraint $c;").mkString("\n")
    s"counter int $counterList;\n\n$automataSection\n\n$constraintSection"
  }
}
