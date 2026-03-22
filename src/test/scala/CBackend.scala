package instar.codegen

import java.nio.charset.StandardCharsets
import java.nio.file.Files
import java.nio.file.Path

import munit.FunSuite
import scala.jdk.CollectionConverters.*
import scala.sys.process.Process
import scala.sys.process.ProcessLogger

import instar.interp.eval
import instar.interp.Value.*
import instar.parser.Parser
import instar.syntax.*
import Expr.*

class CBackendTest extends FunSuite:
  private def evalWithCBackend(src: String): String =
    val result = eval(Parser.parse(src))
    CBackend.compileResult(result)

  private def runCompiledC(cSource: String): String =
    val dir = Files.createTempDirectory("instar-c-")
    val cFile = dir.resolve("program.c")
    val exeFile = dir.resolve("program")

    try
      Files.writeString(cFile, cSource, StandardCharsets.UTF_8)

      val compileLog = new StringBuilder
      val compileCode =
        Process(Seq("cc", "-std=c11", cFile.toString, "-o", exeFile.toString))
          .!(ProcessLogger(line => compileLog.append(line).append('\n')))
      assertEquals(compileCode, 0, clues(compileLog.result()))

      Process(Seq(exeFile.toString)).!!.trim
    finally
      deleteRecursively(dir)

  private def compileAndRunSurface(src: String): String =
    runCompiledC(evalWithCBackend(src))

  private def deleteRecursively(path: Path): Unit =
    if Files.exists(path) then
      Files.walk(path).iterator().asScala.toList.reverse.foreach(Files.deleteIfExists)

  test("compiled simple staged code returns the right value") {
    val out = compileAndRunSurface("lift[2](1) +@2 lift[2](2)")
    assertEquals(out, "3")
  }

  test("compiled closure-converted code preserves captured variables") {
    val src = """
      let mkAdd = lift[2](fun(x: Int @ 2) => lift[2](fun(y: Int @ 2) => x +@2 y)) in
      let add40 = mkAdd(lift[2](40))@2 in
      add40(lift[2](2))@2
    """
    val out = compileAndRunSurface(src)
    assertEquals(out, "42")
  }

  test("compiled recursive closures preserve recursion") {
    val src = """
      let fib = fix[2] fib. lift[2](fun(n: Code[Int]): Code[Int] =>
        if@2 n <=@2 lift[2](1) then lift[2](1) else n *@2 fib(n -@2 lift[2](1))@2)
      in fib(lift[2](5))@2
    """
    val out = compileAndRunSurface(src)
    assertEquals(out, "120")
  }

  test("compiled reference code returns the right value") {
    val value =
      VCode(
        ELet("r", EAlloc(ENum(1), Sta),
          ELet("_", EAssign(EVar("r"), ENum(2), Sta),
            EDeref(EVar("r"), Sta))))
    val out = runCompiledC(CBackend.compile(value))
    assertEquals(out, "2")
  }
