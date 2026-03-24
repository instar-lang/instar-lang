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
import instar.typing.infer

class ExternalTest extends FunSuite:
  private val testsDir = Path.of("tests")

  private val instarFiles =
    Files.list(testsDir).iterator().asScala
      .filter(path => Files.isRegularFile(path) && path.toString.endsWith(".instar"))
      .toList
      .sortBy(_.getFileName.toString)

  assert(instarFiles.nonEmpty, s"No .instar files found under $testsDir")

  private def runCompiledC(cSource: String, stem: String): String =
    val cFile = testsDir.resolve(s"$stem.c")
    val exeFile = testsDir.resolve(stem)
    Files.writeString(cFile, cSource, StandardCharsets.UTF_8)
    instar.compileC(cFile, exeFile)
    instar.runExecutable(exeFile)

  instarFiles.foreach { path =>
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
