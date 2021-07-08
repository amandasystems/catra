package uuverifiers.parikh_theory

trait GraphvizDumper {

  def toDot(): String

  def dumpDotFile(): Unit = dumpDotFile(s"automaton-${this.hashCode()}.dot")

  def dumpDotFile(name: String): Unit = {
    import java.io._

    val file = new File(name)
    val bw = new BufferedWriter(new FileWriter(file))
    bw.write(this.toDot())
    bw.close()
  }

}
