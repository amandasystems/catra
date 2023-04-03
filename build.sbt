import Dependencies._

ThisBuild / scalaVersion := "3.2.2"
ThisBuild / version := "0.1.0-SNAPSHOT"
ThisBuild / organization := "uuverifiers"

ThisBuild / scalacOptions ++= Seq(
  "-deprecation",
  "-unchecked",
  "-Xelide-below",
  "INFO",
  "-source:3.0-migration",
  "-rewrite"
)

// ThisBuild / coverageMinimum := 60
// ThisBuild / coverageFailOnMinimum := false
ThisBuild / coverageExcludedFiles := ".*/src/test/.*"
// ThisBuild / coverageEnabled := true

ThisBuild / resolvers += ("uuverifiers" at "http://logicrunch.research.it.uu.se/maven/")
  .withAllowInsecureProtocol(true)

ThisBuild / libraryDependencies += princess.cross(CrossVersion.for3Use2_13)
ThisBuild / libraryDependencies += fastparse

lazy val root = (project in file("."))
  .settings(
    name := "uuverifiers/catra",
    libraryDependencies += scalaTest % Test,
    libraryDependencies += scalaCheck % Test
  )
