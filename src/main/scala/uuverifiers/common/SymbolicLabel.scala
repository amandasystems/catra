package uuverifiers.common
import scala.language.implicitConversions

sealed abstract class SymbolicLabel
    extends Product
    with Serializable
    with Ordered[SymbolicLabel] {
  def toDotDescription(): String = toString()

  def iterate(): Iterator[Char]
  def subtract(that: SymbolicLabel): SymbolicLabel
  def intersect(that: SymbolicLabel): SymbolicLabel
  def isEmpty(): Boolean
  def contains(ch: Char) = this.overlaps(SymbolicLabel.SingleChar(ch))
  def overlaps(that: SymbolicLabel) = !this.intersect(that).isEmpty()
  def upperBoundExclusive(): Option[Char]
  override def compare(that: SymbolicLabel) = {
    (this.upperBoundExclusive(), that.upperBoundExclusive()) match {
      case (None, None)                       => 0
      case (None, Some(_))                    => 1
      case (Some(_), None)                    => -1
      case (Some(thisBound), Some(thatBound)) => thisBound compareTo thatBound
    }
  }
}

object SymbolicLabel {
  private def isPrintable(c: Char): Boolean = {
    val block = Character.UnicodeBlock.of(c)
    val notSpecial = (!Character.isISOControl(c)) && block != null && (block ne Character.UnicodeBlock.SPECIALS)
    notSpecial && !c.isWhitespace
  }

  private def formatChar(c: Char): String =
    if (isPrintable(c)) c.toString() else c.toInt.toString()
  def apply() = NoChar
  def apply(c: Char) = SingleChar(c)
  def apply(fromInclusive: Char, toInclusive: Char) =
    (fromInclusive, toInclusive) match {
      case (Char.MinValue, Char.MaxValue)    => AnyChar
      case _ if fromInclusive > toInclusive  => NoChar
      case _ if fromInclusive == toInclusive => SingleChar(fromInclusive)
      case _                                 => CharRange(fromInclusive, toInclusive)
    }

  final case object NoChar extends SymbolicLabel {
    override def overlaps(that: SymbolicLabel) = false
    override def intersect(that: SymbolicLabel) = this
    override def isEmpty() = true
    override def subtract(that: SymbolicLabel) = this
    override def upperBoundExclusive() = Some(0.toChar)
    override def iterate() = Iterator()
    override def toString() = "∅"
  }

  final case class SingleChar(c: Char) extends SymbolicLabel with Tracing {
    override def subtract(that: SymbolicLabel) = that match {
      case NoChar          => this
      case AnyChar         => NoChar
      case SingleChar(`c`) => NoChar
      case SingleChar(_)   => this
      case CharRange(from, toInclusive) if c <= toInclusive && from <= c =>
        NoChar
      case CharRange(_, _) => this
      // NOTE: this could be compactified with a final catch-all case, but I
      // avoided that in order to keep this safe against future
      // refactorings. --Amanda
    }

    override def intersect(that: SymbolicLabel) =
      trace(s"${this} ∩ ${that}") {
        that match {
          case AnyChar => this // Redundant but OK
          case SingleChar(otherChar) =>
            if (otherChar == this.c) this else NoChar
          case CharRange(lower, upper) =>
            if (c >= lower && c <= upper) this else NoChar
          case NoChar => NoChar
        }
      }
    override def isEmpty() = false
    override def upperBoundExclusive() = Some((c + 1).toChar)
    override def iterate() = Iterator(c)
    override def toString() = formatChar(c)

  }

  final case class CharRange(from: Char, toInclusive: Char)
      extends SymbolicLabel
      with Tracing {
    override def subtract(that: SymbolicLabel) = ???
    override def intersect(that: SymbolicLabel): SymbolicLabel =
      trace(s"${this} INTERSECTS ${that}") {
        that match {
          case CharRange(thatFrom, thatToInclusive) =>
            SymbolicLabel(thatFrom max from, thatToInclusive min toInclusive)
          case _ => that.intersect(this)
        }
      }
    override def isEmpty() = false
    override def upperBoundExclusive() = Some((toInclusive + 1).toChar)
    override def iterate() = (from to toInclusive).iterator
    override def toString() =
      s"[${formatChar(from)}, ${formatChar(toInclusive)}]"
  }

  final case object AnyChar extends SymbolicLabel {
    override def overlaps(that: SymbolicLabel) = true
    override def intersect(that: SymbolicLabel) = that
    override def isEmpty() = false
    override def subtract(that: SymbolicLabel) = ???
    override def upperBoundExclusive() = None
    override def iterate() = (Char.MinValue to Char.MaxValue).iterator
    override def toString() = "Σ"
  }
}

object SymbolicLabelConversions {
  implicit def charToSymbolicLabel(c: Char): SymbolicLabel = SymbolicLabel(c)
}
