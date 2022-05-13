package uuverifiers.common

import java.io.File
import java.io.BufferedWriter
import java.io.FileWriter

trait GraphvizDumper {

  def toDot(): String

  private def dumpToFile(file: File) = {
    val bw = new BufferedWriter(new FileWriter(file))
    bw.write(this.toDot())
    bw.close()
  }

  def dumpDotFile(): Unit = dumpDotFile(s"automaton-${this.hashCode()}.dot")

  def dumpDotFile(name: String) = dumpToFile(new File(name))

  def dumpDotFile(directory: File, name: String): Unit = {
    assert(directory.isDirectory(), s"${directory} is not a directory!")
    dumpToFile(new File(directory, name))
  }

}
