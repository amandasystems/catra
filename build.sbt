import Dependencies.*

ThisBuild / scalaVersion := "2.13.10"
ThisBuild / version := "0.1.3"
ThisBuild / organization := "uuverifiers"

ThisBuild / scalacOptions ++= Seq(
  "-deprecation",
  //"-Xfatal-warnings",
  "-Xdisable-assertions",
  "-unchecked",
  //"-Xlint",
  "-Xelide-below",
  "INFO",
  "-feature",
  /*"-opt-inline-from:**",
  "-opt:l:method",
  "-opt:l:inline",
  "-opt:unreachable-code",
  "-opt:copy-propagation",
  "-opt:redundant-casts",
  "-opt:box-unbox",
   */
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
    libraryDependencies += scalaCheck % Test,
    assembly / mainClass := Some(
      "uuverifiers.catra.SolveRegisterAutomata"
    )
  )

lazy val benchmark = (project in file("benchmark"))
  .settings(
    name := "catra-benchmark",
    version := s"${version.value}-4", // Version scheme is CATRA version - benchmark version
    assembly / mainClass := Some(
      "uuverifiers.RunBenchmarks"
    )
  ) dependsOn root

lazy val validator = (project in file("validator"))
  .settings(
    name := "catra-validate",
    version := s"${version.value}-5", // Version scheme is CATRA version - validator version
    assembly / mainClass := Some("uuverifiers.Validate")
  ) dependsOn root
