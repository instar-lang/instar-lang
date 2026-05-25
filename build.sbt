val scala3Version = "3.8.0"

ThisBuild / coverageFailOnMinimum := false
ThisBuild / coverageHighlighting := true
ThisBuild / coverageExcludedPackages :=
  "instar\\.experiment\\..*;"

lazy val root = project
  .in(file("."))
  .settings(
    name := "instar-lang",
    version := "0.1.0-SNAPSHOT",

    scalaVersion := scala3Version,

    libraryDependencies += "org.scalameta" %% "munit" % "1.0.0" % Test
  )

addCommandAlias("coverageAll", ";clean;coverage;test;coverageReport;coverageOff")
addCommandAlias(
  "coverageMain",
  ";clean;coverage;testOnly instar.parser.ParserTest instar.interp.* instar.codegen.CBackendTest;coverageReport;coverageOff"
)

Test / parallelExecution := false
