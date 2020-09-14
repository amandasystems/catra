import sbt._

object Dependencies {
  lazy val scalaTest = "org.scalatest" %% "scalatest" % "3.2.0"
  lazy val bricsAutomaton = "dk.brics.automaton" % "automaton" % "1.11-8"
  lazy val princess = "uuverifiers" %% "princess" % "nightly-SNAPSHOT"
}
