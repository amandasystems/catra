package uuverifiers.catra

import scala.annotation.tailrec

sealed trait ValidationResult
case object Valid extends ValidationResult
sealed case class Invalid(motivation: String) extends ValidationResult

trait InputValidating {

  /**
   * Ensure that each automata has unique counter values.
   * @param i The instance to validate
   * @return
   */
  private def noOverlappingCounters(i: Instance): ValidationResult = {
    val automataCounters: Seq[Set[Counter]] = i.automata.flatMap { group =>
      group.map(
        _.transitions.flatMap(t => i.transitionToOffsets(t).keys).toSet
      )
    }

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
    Seq(noOverlappingCounters)

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
