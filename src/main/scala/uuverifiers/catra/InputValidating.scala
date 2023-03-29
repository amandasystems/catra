package uuverifiers.catra

import scala.annotation.tailrec

sealed trait ValidationResult
case object Valid extends ValidationResult
sealed case class Invalid(motivation: String) extends ValidationResult

trait InputValidating {

  private def warnUndeclaredCounter(
      usedHow: String
  )(undeclaredCounter: Counter) =
    Invalid(s"Counter $undeclaredCounter $usedHow but never declared")

  private def counterOnlyDeclaredOnce(i: Instance): ValidationResult =
    i.counters.groupBy(identity).filter(_._2.size > 1).keys.toSeq match {
      case Nil => Valid
      case duplicates =>
        Invalid(
          s"Counter${if (duplicates.size > 1) "s" else ""} declared more than once: ${duplicates.mkString(", ")}"
        )
    }

  private def undeclaredCounter(i: Instance)(c: Counter): Boolean =
    !(i.counters contains c)

  private def onlyDeclaredCountersIncremented(i: Instance): ValidationResult = {
    i.automataProducts
      .flatMap(automata => automata.flatMap(_.counters()))
      .find(undeclaredCounter(i))
      .map(warnUndeclaredCounter("incremented"))
      .getOrElse(Valid)
  }

  private def onlyDeclaredCountersUsedInConstraints(
      i: Instance
  ): ValidationResult = {
    i.constraints
      .flatMap(f => f.counters())
      .find(undeclaredCounter(i))
      .map(warnUndeclaredCounter("constrained"))
      .getOrElse(Valid)
  }

  // FIXME warn about empty groups!
  /**
   * Ensure that each automata has unique counter values.
   * @param i The instance to validate
   * @return
   */
  private def noOverlappingCounters(i: Instance): ValidationResult = {
    val automataCounters: Seq[Set[Counter]] =
      i.automataProducts.flatMap(product => product.map(_.counters()))

    val counterCounts: Map[Counter, Int] =
      automataCounters.foldLeft(Map[Counter, Int]()) {
        (countSoFar, automataCounters) =>
          var updatedCounts = countSoFar

          automataCounters.foreach { counter =>
            updatedCounts = updatedCounts.updatedWith(counter) {
              case None                => Some(1)
              case Some(previousValue) => Some(previousValue + 1)
            }
          }
          updatedCounts
      }

    val overlaps = counterCounts.view.filter { case (_, count) => count > 1 }

    if (overlaps.isEmpty) {
      Valid
    } else {
      val overlapList = overlaps
        .map { case (counter, nrUses) => s"$counter: $nrUses" }
        .mkString(", ")
      val motivation = s"overlapping counters between automata: $overlapList"
      Invalid(motivation)
    }
  }

  private def rules: Seq[Instance => ValidationResult] =
    Seq(
      onlyDeclaredCountersIncremented,
      onlyDeclaredCountersUsedInConstraints,
      noOverlappingCounters,
      counterOnlyDeclaredOnce
    )

  @tailrec
  private def applyRules(
      i: Instance,
      rulesLeft: Seq[Instance => ValidationResult] = rules,
      previousResult: ValidationResult = Valid
  ): ValidationResult = (rulesLeft, previousResult) match {
    case (_, result: Invalid) => result
    case (Seq(), result)      => result
    case (rule +: remainingRules, Valid) =>
      applyRules(i, remainingRules, rule(i))
  }

  def validate(i: Instance): ValidationResult = applyRules(i)
}
