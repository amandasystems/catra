import sbt._

object Dependencies {
  lazy val scalaTest = "org.scalatest" %% "scalatest" % "3.2.15"
  lazy val scalaCheck = "org.scalatestplus" %% "scalacheck-1-17" % "3.2.15.0"
  lazy val princess = "uuverifiers" %% "princess" % "2022-11-03-amanda-1"
  lazy val fastparse = "com.lihaoyi" %% "fastparse" % "3.0.1"
}
