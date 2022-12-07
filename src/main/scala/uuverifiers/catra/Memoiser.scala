package uuverifiers.catra

import scala.collection.mutable
import scala.ref.WeakReference

final class Memoiser[K, V] {
  // This is a maximally weak container.
  private var memory = WeakReference(mutable.WeakHashMap[K, V]())

  private def getOrCreateCache(): mutable.WeakHashMap[K, V] =
    memory.get match {
      case None =>
        val newMem = mutable.WeakHashMap[K, V]()
        memory = WeakReference(newMem)
        newMem
      case Some(cache) => cache
    }

  def remember(input: K)(computeResults: => V): V =
    getOrCreateCache().getOrElseUpdate(input, computeResults)
}
