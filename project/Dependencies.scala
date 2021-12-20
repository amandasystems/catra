import sbt._

object Dependencies {
  lazy val scalaTest = "org.scalatest" %% "scalatest" % "3.2.0"
  lazy val scalaCheck = "org.scalatestplus" %% "scalacheck-1-15" % "3.2.2.0"
  lazy val princess = "uuverifiers" %% "princess" % "nightly-SNAPSHOT"
  lazy val fastparse = "com.lihaoyi" %% "fastparse" % "2.2.2"
}
