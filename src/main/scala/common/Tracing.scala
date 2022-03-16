package uuverifiers.common
import scala.annotation.elidable
import scala.annotation.elidable.FINE
import collection.mutable.HashMap


object Statistics {
  private val dynTraceEnable = sys.env
    .getOrElse("OSTRICH_STATS", "FALSE")
    .toUpperCase() == "TRUE"

  private def report(stats: Statistics) = {
    // import java.io._

    // val file = new File("ostrich-stats.txt")
    // val bw = new BufferedWriter(new FileWriter(file, true))
    // bw.write("stats" + stats.counter + "\n")
    // bw.close()
    if (dynTraceEnable) System.err.println("stats" + stats.counter) // FIXME
  }
}

class Statistics() {
  private val counter = HashMap[String, Int]()

  @elidable(FINE)
  def increment(key: String) = counter(key) = counter.getOrElse(key, 0) + 1

  @elidable(FINE)
  def report() = Statistics.report(this)
}

// TODO convert this to a hierarchical logger writing to some file somewhere
trait Tracing {

  def enableTracing(verbose: Boolean = true) = {
    dynTraceEnable = verbose
    this
  }

  protected var dynTraceEnable = sys.env
    .getOrElse("CATRA_TRACE", "FALSE")
    .toUpperCase() == "TRUE"

  lazy private val context = this.getClass.getName

  @elidable(FINE)
  protected def logInfo(message: String) =
    if (dynTraceEnable) System.err.println(message)

  @elidable(FINE)
  protected def logException(e: Throwable) =
    e.printStackTrace()

  protected def trace[T](message: String = "")(something: T): T = {
    logInfo(s"trace::${context}::${message}(${something})")

    something
  }
}
