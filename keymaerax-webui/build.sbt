import java.io.{BufferedReader, FileReader}

name := "KeYmaeraX-Web"

version := new BufferedReader(new FileReader("keymaerax-core/src/main/resources/VERSION")).readLine()

//scalacOptions ++= Seq("-Xno-patmat-analysis")

resolvers += "Sonatype OSS Snapshots" at "https://oss.sonatype.org/content/repositories/snapshots" // ScalaMeter

assemblyJarName in (Test, assembly) := s"keymaerax-${version.value}.jar"

scalacOptions in (Compile, doc) ++= Seq("-doc-root-content", "rootdoc.txt")

libraryDependencies += "org.scala-lang" % "scala-reflect" % "2.12.8"

libraryDependencies += "org.scala-lang" % "scala-compiler" % "2.12.8"

libraryDependencies += "org.scalatest" %% "scalatest" % "3.0.5" % "test"

libraryDependencies += "org.scalamock" %% "scalamock" % "4.4.0" % "test"

libraryDependencies += "io.monix" %% "monix" % "2.3.3"

libraryDependencies += "org.pegdown" % "pegdown" % "1.6.0" % "test"      // (For Html Scalatest reports)

libraryDependencies += "com.jsuereth" %% "scala-arm" % "2.0" // automatic resource management

/// sqlite driver

libraryDependencies += "com.typesafe.slick" %% "slick" % "2.1.0"

libraryDependencies += "com.typesafe.slick" %% "slick-codegen" % "2.1.0"

libraryDependencies += "org.xerial" % "sqlite-jdbc" % "3.27.2"

////////////////////////////////////////////////////////////////////////////////
// HyDRA Settings
// Taken from https://www.assembla.com/wiki/show/liftweb/using_sbt
////////////////////////////////////////////////////////////////////////////////

resolvers += "Typesafe Repo" at "http://repo.typesafe.com/typesafe/releases/" // contains json-schema-validtor.

scalacOptions := Seq("-unchecked", "-deprecation", "-encoding", "utf8")

javaOptions += "-Xss20M"

//region Akka

val akkaV = "2.5.23"

libraryDependencies += "com.typesafe.akka" %% "akka-http"   % "10.1.8"

libraryDependencies += "com.typesafe.akka" %% "akka-http-xml" % "10.1.8"

libraryDependencies += "com.typesafe.akka" %% "akka-stream" % akkaV

libraryDependencies += "io.spray" %% "spray-json" % "1.3.4"

libraryDependencies += "com.typesafe.akka" %% "akka-http-spray-json" % "10.1.8"

libraryDependencies += "com.typesafe.akka"   %% "akka-slf4j"     % akkaV

resolvers += Resolver.sonatypeRepo("releases")
addCompilerPlugin("org.scalamacros" % "paradise" % "2.1.0" cross CrossVersion.full)

//endregion

////////////////////////////////////////////////////////////////////////////////
// Continuous testing/running settings (i.e., defining behavior of the ~
// command
////////////////////////////////////////////////////////////////////////////////

watchSources ++= {{ baseDirectory map {
  path => ((path / "src/main/resources/partials/") ** "*.html").get 
}}.value }

watchSources ++= {{ baseDirectory map {
  path => ((path / "src/main/resources/js") ** "*.js").get 
}}.value }

watchSources ++= {{baseDirectory map {
  path => ((path / "src/main/resources") ** "*.html").get 
}}.value }


////////////////////////////////////////////////////////////////////////////////
// Unit testing
////////////////////////////////////////////////////////////////////////////////

parallelExecution in Test := false

// set fork to true in order to run tests in their own Java process.
// not forking avoids broken pipe exceptions in test reporter, but forking might become necessary in certain
// multithreaded setups (see ScalaTest documentation)
fork in Test := false

// set HTML test report output directory
testOptions in Test += Tests.Argument(TestFrameworks.ScalaTest, "-h", "target/test-reports")

// record and report test durations
testOptions in Test += Tests.Argument(TestFrameworks.ScalaTest, "-oD")

// report long-running tests (report every hour for tests that run longer than 1hr)
testOptions in Test += Tests.Argument(TestFrameworks.ScalaTest, "-W", "3600", "3600")

testFrameworks += new TestFramework("org.scalameter.ScalaMeterFramework")

logBuffered := false

////////////////////////////////////////////////////////////////////////////////
// Builds -- make sure you are using SBT 13.6+
////////////////////////////////////////////////////////////////////////////////

// command line UI
mainClass in assembly := Some("edu.cmu.cs.ls.keymaerax.launcher.Main")

// do not run tests when building assembly
test in assembly := {}
