package instar

import java.nio.charset.StandardCharsets
import java.nio.file.Files
import java.nio.file.Path

import scala.sys.process.Process
import scala.sys.process.ProcessLogger

import instar.codegen.CBackend
import instar.interp.eval
import instar.interp.Value.VCode
import instar.parser.Parser

def main(args: Array[String]): Unit =
  args.toList match
    case "--emit-c" :: file :: Nil =>
      emitC(Path.of(file))
    case file :: Nil =>
      runFile(Path.of(file))
    case _ =>
      Console.err.println("Usage: Main [--emit-c] <source-file>")

def runFile(path: Path): Unit =
  try
    val source = Files.readString(path, StandardCharsets.UTF_8)
    val program = Parser.parse(source)
    val (value, _) = eval(program)
    println(value)
  catch
    case ex: Exception =>
      Console.err.println(s"Failed to run ${path.toAbsolutePath}: ${ex.getMessage}")

def emitC(path: Path): Unit =
  try
    val source = Files.readString(path, StandardCharsets.UTF_8)
    val program = Parser.parse(source)
    val result @ (value, _) = eval(program)
    value match
      case VCode(_) =>
        val cFile = cOutputPath(path)
        val exeFile = executableOutputPath(path)
        val code = CBackend.compileResult(result)
        Files.writeString(cFile, code, StandardCharsets.UTF_8)
        println(s"Wrote C code to ${cFile.toAbsolutePath}")
        compileC(cFile, exeFile)
        println(s"Built executable at ${exeFile.toAbsolutePath}")
        println(runExecutable(exeFile))
      case other =>
        Console.err.println(s"Expected the program to evaluate to VCode, found $other")
  catch
    case ex: Exception =>
      Console.err.println(s"Failed to compile ${path.toAbsolutePath}: ${ex.getMessage}")

def cOutputPath(path: Path): Path =
  path.resolveSibling(replaceExtension(path.getFileName.toString, "c"))

def executableOutputPath(path: Path): Path =
  path.resolveSibling(replaceExtension(path.getFileName.toString, "out"))

private def replaceExtension(fileName: String, newExt: String): String =
  val dot = fileName.lastIndexOf('.')
  if dot > 0 then s"${fileName.substring(0, dot)}.$newExt"
  else s"$fileName.$newExt"

private def compileC(cFile: Path, exeFile: Path): Unit =
  val compileLog = new StringBuilder
  val exitCode =
    Process(Seq("cc", "-std=c11", cFile.toString, "-o", exeFile.toString))
      .!(ProcessLogger(line => compileLog.append(line).append('\n')))
  if exitCode != 0 then
    val details =
      val log = compileLog.result().trim
      if log.isEmpty then s"C compiler exited with code $exitCode"
      else log
    throw RuntimeException(details)

private def runExecutable(exeFile: Path): String =
  Process(Seq(exeFile.toString)).!!.trim
