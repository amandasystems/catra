package uuverifiers.common

sealed case class ProductState(left: State, right: State) extends State {
  override def isProductOf(ts: State): Boolean =
    (left isProductOf ts) || (right isProductOf ts)
  override def toPretty(): String = s"${left.toPretty()} && ${right.toPretty()}"
  override def toDotLabel(): String = s"${left.toDotLabel()}_AND_${right.toDotLabel()}"
}

sealed trait State {
  def isProductOf(ts: State): Boolean = ts == this
  def intersect(right: State): ProductState = ProductState(this, right)
  def toPretty(): String
  def toDotLabel(): String
  override def toString: String = toPretty()
}

sealed case class IntState(id: Int) extends State with Ordered[IntState] {
  def compare(that: IntState): Int = this.id compare that.id
  def successor(): IntState = IntState(id + 1)
  override def toDotLabel(): String = toPretty()
  override def toPretty(): String = s"s$id"
}

object IntState {
  def apply(range: Range): IndexedSeq[IntState] = range.map(IntState(_))
  def apply(ids: Int*): Seq[IntState] = ids.map(IntState(_))
}
