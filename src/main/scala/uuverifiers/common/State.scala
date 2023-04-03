package uuverifiers.common

sealed case class ProductState(left: State, right: State) extends State {
  override def isProductOf(ts: State): Boolean =
    (left isProductOf ts) || (right isProductOf ts)
  override def toDotDescription(): String =
    s"${left.toDotDescription()} && ${right.toDotDescription()}"
  override def toDotIdentifier(): String = {
    s"${left.toDotIdentifier()}_AND_${right.toDotIdentifier()}"

  }

  override def compare(that: State): Int = that match {
    case that: ProductState => (left, right) compare (that.left, that.right)
    // We sort before everything else
    case _ => 1
  }
}

// Order is: states are internally ordered, Product states are largest,
// followed by string states, followed by integer states.
sealed trait State extends Ordered[State] {
  def isProductOf(ts: State): Boolean = ts == this
  def intersect(right: State): ProductState = ProductState(this, right)
  def toDotDescription(): String
  def toDotIdentifier(): String
  override def toString: String = toDotDescription()
}

sealed case class IntState(id: Int) extends State {
  override def compare(that: State): Int = that match {
    case other: IntState => this.id compare other.id
    case _: StringState  => -1
    case _: ProductState => -1

  }
  def successor(): IntState = IntState(id + 1)
  override def toDotIdentifier(): String = toDotDescription()
  override def toDotDescription(): String = s"s$id"
}

sealed class StringState(private val label: String) extends State {
  override def toDotDescription(): String = label
  override def toDotIdentifier(): String = label
  override def compare(that: State): Int = that match {
    case that: StringState => this.label compare that.label
    case _: IntState       => 1
    case _: ProductState   => -1
  }
}

object IntState {
  def apply(range: Range): IndexedSeq[IntState] = range.map(IntState(_))
  def apply(ids: Int*): Seq[IntState] = ids.map(IntState(_))
}
