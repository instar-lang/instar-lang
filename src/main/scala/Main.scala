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

private case class CliConfig(
  emitC: Boolean,
  file: Option[Path],
  program: Option[String],
)

def main(args: Array[String]): Unit =
  parseArgs(args.toList) match
    case Left(message) =>
      Console.err.println(message)
    case Right(config) =>
      config match
        case CliConfig(true, Some(path), None) =>
          emitCFromPath(path)
        case CliConfig(false, Some(path), None) =>
          runFile(path)
        case CliConfig(true, None, Some(program)) =>
          emitCFromProgram(program)
        case CliConfig(false, None, Some(program)) =>
          runProgram(program)
        case _ =>
          Console.err.println(usage)

def runFile(path: Path): Unit =
  try
    val source = Files.readString(path, StandardCharsets.UTF_8)
    runSource(source, s"Error: Failed to run ${path.toAbsolutePath}")
  catch
    case ex: Exception =>
      Console.err.println(s"Error: Failed to run ${path.toAbsolutePath}: ${ex.getMessage}")

def runProgram(source: String): Unit =
  try
    runSource(source, "Error: Failed to run inline program")
  catch
    case ex: Exception =>
      Console.err.println(s"Error: Failed to run inline program: ${ex.getMessage}")

def emitCFromPath(path: Path): Unit =
  try
    val source = Files.readString(path, StandardCharsets.UTF_8)
    emitCSource(source, cOutputPath(path), executableOutputPath(path), s"Error: Failed to compile ${path.toAbsolutePath}")
  catch
    case ex: Exception =>
      Console.err.println(s"Error: Failed to compile ${path.toAbsolutePath}: ${ex.getMessage}")

def emitCFromProgram(source: String): Unit =
  try
    val cFile = inlineCOutputPath
    val exeFile = inlineExecutableOutputPath
    emitCSource(source, cFile, exeFile, "Error: Failed to compile inline program")
  catch
    case ex: Exception =>
      Console.err.println(s"Error: Failed to compile inline program: ${ex.getMessage}")

private def runSource(source: String, errorPrefix: String): Unit =
  try
    val program = Parser.parse(source)
    val (value, _) = eval(program)
    println(value)
  catch
    case ex: Exception =>
      Console.err.println(s"$errorPrefix: ${ex.getMessage}")

private def emitCSource(source: String, cFile: Path, exeFile: Path, errorPrefix: String): Unit =
  try
    val program = Parser.parse(source)
    val result @ (value, _) = eval(program)
    value match
      case VCode(_) =>
        val code = CBackend.compileResult(result)
        Files.writeString(cFile, code, StandardCharsets.UTF_8)
        println(s"Wrote C code to ${cFile.toAbsolutePath}")
        compileC(cFile, exeFile)
        println(s"Built executable at ${exeFile.toAbsolutePath}")
        println(runExecutable(exeFile))
      case other =>
        Console.err.println(s"Error: Expected the program to evaluate to VCode, found $other")
  catch
    case ex: Exception =>
      Console.err.println(s"$errorPrefix: ${ex.getMessage}")

def cOutputPath(path: Path): Path =
  path.resolveSibling(replaceExtension(path.getFileName.toString, "c"))

def executableOutputPath(path: Path): Path =
  path.resolveSibling(replaceExtension(path.getFileName.toString, "out"))

def inlineCOutputPath: Path = Path.of("instar_inline.c").toAbsolutePath

def inlineExecutableOutputPath: Path = Path.of("instar_inline.out").toAbsolutePath

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

private def parseArgs(args: List[String]): Either[String, CliConfig] =
  def loop(rest: List[String], emitC: Boolean, file: Option[Path], program: Option[String]): Either[String, CliConfig] =
    rest match
      case Nil =>
        Right(CliConfig(emitC, file, program))
      case "--emit-c" :: tail =>
        loop(tail, emitC = true, file, program)
      case ("--program" | "-e") :: src :: tail =>
        if file.nonEmpty then Left("Pass either a source file or `--program`, not both.\n" + usage)
        else if program.nonEmpty then Left("`--program` was provided more than once.\n" + usage)
        else loop(tail, emitC, file, Some(src))
      case flag :: _ if flag.startsWith("-") =>
        Left(s"Unknown option `$flag`.\n$usage")
      case path :: tail =>
        if program.nonEmpty then Left("Pass either a source file or `--program`, not both.\n" + usage)
        else if file.nonEmpty then Left("Pass exactly one source file.\n" + usage)
        else loop(tail, emitC, Some(Path.of(path)), program)

  loop(args, emitC = false, file = None, program = None).flatMap {
    case config @ CliConfig(_, Some(_), None) => Right(config)
    case config @ CliConfig(_, None, Some(_)) => Right(config)
    case _ => Left(usage)
  }

private val usage =
  "Usage: Main [--emit-c] <source-file>\n" +
    "   or: Main [--emit-c] --program <source>\n" +
    "   or: Main [--emit-c] -e <source>"
