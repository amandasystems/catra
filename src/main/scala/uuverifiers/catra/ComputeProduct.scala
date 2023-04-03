package uuverifiers.catra

import fastparse.Parsed
import uuverifiers.catra.SolveRegisterAutomata.measureTime

import scala.io.Source

object ComputeProduct {

  val Parsed.Success(instance, _) = {
    val inputFileHandle = Source.fromFile("basket/18.par")
    val instance = InputFileParser.parse(inputFileHandle.mkString(""))
    inputFileHandle.close()
    instance
  }: @unchecked
  println("Computing all products...")
  instance.automataProducts.zipWithIndex.foreach {
    case (productGroup, i) if productGroup.size > 1 =>
      print(s"Computing product $i (size=${productGroup.size})...")
      val (_, time) = measureTime(productGroup.take(9).reduce(_ productWith _))
      println(
        s"...done in $time seconds!"
      )
    case _ => ()
  }
}
