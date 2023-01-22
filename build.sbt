name := "string example"

version := "0.1"

scalaVersion := "2.11.8"

resolvers += ("uuverifiers" at "http://logicrunch.research.it.uu.se/maven/").withAllowInsecureProtocol(true)

libraryDependencies += "uuverifiers" %% "princess" % "nightly-SNAPSHOT"

libraryDependencies += "org.sat4j" % "org.sat4j.core" % "2.3.1"
