name := "kardinal"

version := "0.0.1"

scalaVersion := "2.13.1"

organization := "ch.epfl.lara"

libraryDependencies += "org.scalactic" %% "scalactic" % "3.0.8"
libraryDependencies += "org.scalatest" %% "scalatest" % "3.0.8" % "test"

mainClass := Some("kardinal.App")

// resolvers ++= Seq("snapshots"     at "http://oss.sonatype.org/content/repositories/snapshots",
//                   "releases"      at "http://oss.sonatype.org/content/repositories/releases")
 
scalacOptions ++= Seq("-unchecked", "-deprecation")
