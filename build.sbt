import Dependencies._

ThisBuild / scalaVersion := "2.13.5"
ThisBuild / version := "0.1.0-SNAPSHOT"
ThisBuild / organization := "uuverifiers"

ThisBuild / scalacOptions ++= Seq(
  "-deprecation",
  //"-Xfatal-warnings",
  "-unchecked",
  "-Xlint",
  // "-Xelide-below",
  // "INFO",
  "-feature",
  "-opt-inline-from:**",
  "-opt:l:method",
  "-opt:l:inline",
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
    name := "catra",
    libraryDependencies += scalaTest % Test,
    libraryDependencies += scalaCheck % Test
  )