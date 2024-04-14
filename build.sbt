name := "seq-solver"

version := "0.1"

scalaVersion := "2.13.13"

Compile / mainClass := Some("seqSolver.SeqSolverMain")

resolvers += "uuverifiers" at "https://eldarica.org/maven/"

libraryDependencies += "uuverifiers" %% "princess" % "nightly-SNAPSHOT"

libraryDependencies += "org.sat4j" % "org.sat4j.core" % "2.3.1"
