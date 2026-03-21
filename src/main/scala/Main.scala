package instar

import java.nio.charset.StandardCharsets
import java.nio.file.Files
import java.nio.file.Path

import instar.interp.eval
import instar.parser.Parser

def main(args: Array[String]): Unit =
  args.toList match
    case file :: Nil =>
      runFile(Path.of(file))
    case _ =>
      Console.err.println("Usage: Main <source-file>")

def runFile(path: Path): Unit =
  try
    val source = Files.readString(path, StandardCharsets.UTF_8)
    val program = Parser.parse(source)
    val (value, _) = eval(program)
    println(value)
  catch
    case ex: Exception =>
      Console.err.println(s"Failed to run ${path.toAbsolutePath}: ${ex.getMessage}")
