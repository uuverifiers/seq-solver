name := "string example"

version := "1.0"

scalaVersion := "2.11.8"

resolvers += ("uuverifiers" at "http://logicrunch.research.it.uu.se/maven/").withAllowInsecureProtocol(true)

libraryDependencies += "uuverifiers" %% "ostrich" % "nightly-SNAPSHOT"
