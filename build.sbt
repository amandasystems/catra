import Dependencies._
import scala.sys.process.Process

val gitCommit = Process("git rev-parse --short HEAD").lineStream.head

ThisBuild / scalaVersion := "2.13.10"
ThisBuild / version := gitCommit
ThisBuild / organization := "uuverifiers"

ThisBuild / scalacOptions ++= Seq(
  "-deprecation",
  //"-Xfatal-warnings",
  "-unchecked",
  "-Xlint",
   "-Xelide-below",
   "INFO",
  "-feature",
  "-opt-inline-from:**",
  "-opt:l:method",
  "-opt:l:inline",
  "-opt:unreachable-code",
  "-opt:copy-propagation",
  "-opt:redundant-casts",
  "-opt:box-unbox",
  "-Ywarn-dead-code",
  "-Ywarn-unused"
)

// ThisBuild / coverageMinimum := 60
// ThisBuild / coverageFailOnMinimum := false
ThisBuild / coverageExcludedFiles := ".*/src/test/.*"
// ThisBuild / coverageEnabled := true

ThisBuild / resolvers += ("uuverifiers" at "http://logicrunch.research.it.uu.se/maven/")
  .withAllowInsecureProtocol(true)

ThisBuild / libraryDependencies += princess
ThisBuild / libraryDependencies += fastparse

lazy val root = (project in file("."))
  .settings(
    name := "uuverifiers/catra",
    libraryDependencies += scalaTest % Test,
    libraryDependencies += scalaCheck % Test
  )
