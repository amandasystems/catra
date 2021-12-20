package uuverifiers.parikh_theory

sealed case class CommandLineOptions(inputFile: String)

object CommandLineOptions {
  def parse(args: Array[String]) = CommandLineOptions(inputFile = args(1))
}
