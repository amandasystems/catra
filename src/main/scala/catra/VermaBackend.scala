package uuverifiers.catra

import scala.util.Try
import uuverifiers.common.Tracing

class VermaBackend(private val arguments: CommandLineOptions)
    extends Backend
    with Tracing {

  import arguments._

  override def solveSatisfy(instance: Instance): Try[SatisfactionResult] = ???

  override def findImage(instance: Instance): Try[ImageResult] = ???

}
