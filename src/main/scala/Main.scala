package instar

import java.nio.charset.StandardCharsets
import java.nio.file.Files
import java.nio.file.Path

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
        println(s"Generated code: $value")
        val output = cOutputPath(path)
        val code = CBackend.compileResult(result)
        Files.writeString(output, code, StandardCharsets.UTF_8)
        println(s"Emitting C code for ${path.toAbsolutePath}...")
      case other =>
        Console.err.println(s"Expected the program to evaluate to VCode, found $other")
  catch
    case ex: Exception =>
      Console.err.println(s"Failed to compile ${path.toAbsolutePath}: ${ex.getMessage}")

def cOutputPath(path: Path): Path =
  val fileName = path.getFileName.toString
  val dot = fileName.lastIndexOf('.')
  val outName =
    if dot > 0 then s"${fileName.substring(0, dot)}.c"
    else s"$fileName.c"
  path.resolveSibling(outName)
