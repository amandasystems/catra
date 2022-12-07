package uuverifiers.common

import scala.collection.mutable

object ClosureComputation {
  def computeClosure[T](
      startingFrom: Set[T],
      findMoreFrom: T => Iterable[T],
      seen: mutable.HashSet[T] = mutable.HashSet[T]()
  ): mutable.HashSet[T] = {
    val todo: mutable.Queue[T] =
      new mutable.Queue(startingFrom.size).addAll(startingFrom)

    while (todo.nonEmpty) {
      val current = todo.dequeue()
      seen add current
      todo enqueueAll findMoreFrom(current).filterNot(seen.contains).toSet
    }
    seen
  }
}
