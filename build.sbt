name := "kardinal"

version := "0.0.1"

scalaVersion := "2.13.1"

organization := "ch.epfl.lara"

libraryDependencies += "org.scalactic" %% "scalactic" % "3.0.8"
libraryDependencies += "org.scalatest" %% "scalatest" % "3.0.8" % "test"

mainClass in (Compile, run) := Some("kardinal.App")

resolvers ++= Seq(//"snapshots"     at "https://oss.sonatype.org/content/repositories/snapshots",
                  "releases"      at "https://oss.sonatype.org/content/repositories/releases")

libraryDependencies += "com.storm-enroute" %% "scalameter" % "0.19"

testFrameworks += new TestFramework("org.scalameter.ScalaMeterFramework")

logBuffered := false
parallelExecution in Test := false

scalacOptions ++= Seq("-unchecked", "-deprecation")
