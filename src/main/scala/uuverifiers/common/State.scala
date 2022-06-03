package uuverifiers.common

sealed case class ProductState(left: State, right: State) extends State {
  override def isProductOf(ts: State): Boolean =
    (left isProductOf ts) || (right isProductOf ts)
  override def toDotDescription(): String = s"${left.toDotDescription()} && ${right.toDotDescription()}"
  override def toDotIdentifier(): String = s"${left.toDotIdentifier()}_AND_${right.toDotIdentifier()}"
}

sealed trait State {

  def isProductOf(ts: State): Boolean = ts == this
  def intersect(right: State): ProductState = ProductState(this, right)
  def toDotDescription(): String
  def toDotIdentifier(): String
  override def toString: String = toDotDescription()
}

sealed case class IntState(id: Int) extends State with Ordered[IntState] {
  def compare(that: IntState): Int = this.id compare that.id
  def successor(): IntState = IntState(id + 1)
  override def toDotIdentifier(): String = toDotDescription()
  override def toDotDescription(): String = s"s$id"
}

sealed class StringState(label: String) extends State {
  override def toDotDescription(): String = label
  override def toDotIdentifier(): String = label
}

object IntState {
  def apply(range: Range): IndexedSeq[IntState] = range.map(IntState(_))
  def apply(ids: Int*): Seq[IntState] = ids.map(IntState(_))
}
