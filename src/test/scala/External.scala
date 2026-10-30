package instar.external

import java.nio.charset.StandardCharsets
import java.nio.file.Files
import java.nio.file.Path

import scala.jdk.CollectionConverters.*
import scala.sys.process.Process
import scala.sys.process.ProcessLogger

import munit.FunSuite

import instar.codegen.CBackend
import instar.interp.eval
import instar.parser.parse
import instar.typing.Elaboration.infer

class ExternalTest extends FunSuite:
  private val testsDir = Path.of("tests")
  // Leave this empty to run every `tests/*.instar` case.
  // Otherwise list the file stems or filenames to be tested
  private val requestedTestFiles: List[String] =
    List("power.instar", "fib.instar", "mkAdd.instar", "impPower.instar", "try.instar")
  // TODO: ackermann doesn't work yet because we don't support recursive definitions

  private val allInstarFiles =
    Files.list(testsDir).iterator().asScala
      .filter(path => Files.isRegularFile(path) && path.toString.endsWith(".instar"))
      .toList
      .sortBy(_.getFileName.toString)

  private val selectedInstarFiles =
    if requestedTestFiles.nonEmpty then requestedTestFiles.map(resolveRequestedFile)
    else allInstarFiles

  private def resolveRequestedFile(name: String): Path =
    val provided = Path.of(name)
    val withExt =
      if name.endsWith(".instar") then provided
      else Path.of(s"$name.instar")

    val candidate =
      if withExt.isAbsolute then withExt
      else
        val direct = testsDir.resolve(withExt)
        if Files.exists(direct) then direct else withExt

    if Files.isRegularFile(candidate) then candidate.normalize()
    else fail(s"Requested external test file `$name` was not found")

  private def runCompiledC(cSource: String, stem: String): String =
    val cFile = testsDir.resolve(s"$stem.c")
    val exeFile = testsDir.resolve(stem)
    Files.writeString(cFile, cSource, StandardCharsets.UTF_8)
    instar.compileC(cFile, exeFile)
    instar.runExecutable(exeFile)

  selectedInstarFiles.foreach { path =>
    test(s"external file: ${path.getFileName}") {
      val src = Files.readString(path, StandardCharsets.UTF_8)
      val parsed = parse(src)
      val typed = infer(parsed)
      val evaluated = eval(typed)
      val cSource = CBackend.compileResult(evaluated)
      val output = runCompiledC(cSource, path.getFileName.toString.stripSuffix(".instar"))

      assert(output.nonEmpty, clues(s"compiled program for ${path.getFileName} produced empty stdout"))
    }
  }
