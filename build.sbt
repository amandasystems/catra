import Dependencies._

ThisBuild / scalaVersion     := "2.12.12"
ThisBuild / version          := "0.1.0-SNAPSHOT"
ThisBuild / organization     := "uuverifiers"

ThisBuild / scalacOptions ++= Seq(
    "-deprecation",
    // "-Xfatal-warnings",
    "-unchecked",
    "-Xlint",
    "-Xelide-below", "INFO",
    // "-feature",
    "-opt:l:inline",
    "-opt-inline-from:**",
    "-Ywarn-dead-code",
    "-Ywarn-unused"
)

ThisBuild / resolvers += ("uuverifiers" at "http://logicrunch.research.it.uu.se/maven/")
  .withAllowInsecureProtocol(true)

ThisBuild / libraryDependencies += bricsAutomaton
ThisBuild / libraryDependencies += princess

// Tests run at maximum verbosity (this is untested and a pretty stupid
// configuration, but may work). It's also the only way of doing this because
// SBT is bonkers. cf. https://stackoverflow.com/a/43397744
Test / scalacOptions --= Seq(
  "-Xelide-below", "INFO")
Test / scalacOptions ++= Seq(
  "-Xelide-below", "0")

lazy val root = (project in file("."))
  .settings(
    name := "Parikh Theory",
    libraryDependencies += scalaTest % Test
  )
