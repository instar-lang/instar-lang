package instar

import java.nio.charset.StandardCharsets
import java.nio.file.Files
import java.nio.file.Path

import scala.sys.process.Process
import scala.sys.process.ProcessLogger

import instar.codegen.CBackend
import instar.interp.eval
import instar.interp.Store
import instar.interp.Value
import instar.interp.Value.*
import instar.parser.parse
import instar.typing.*

def main(args: Array[String]): Unit =
  parseArgs(args.toList)
  val source =
    if Config.sourceFile.nonEmpty then
      Files.readString(Config.sourceFile.get, StandardCharsets.UTF_8)
    else if Config.program.nonEmpty then
      Config.program.get
    else throw new IllegalStateException("No source provided")
  val (v, s) = runSource(source)
  if Config.emitC then
    val cFile =
      if Config.sourceFile.nonEmpty then cOutputPath(Config.sourceFile.get)
      else inlineCOutputPath
    val exeFile =
      if Config.sourceFile.nonEmpty then executableOutputPath(Config.sourceFile.get)
      else inlineExecutableOutputPath
    emitCSource(v, s, cFile, exeFile)

private def runSource(source: String): (Value, Store) =
  val prog = if Config.brackets
             then bracketparser.translate(bracketparser.parse(source))
             else parse(source)
  println(s"========Parsed Program=========")
  println(s"$prog")
  val tyProg = infer(prog)
  println(s"========Elaborated Program=========")
  println(s"$tyProg")
  println(s"========Type Checking Result=========")
  println(s"${tyProg.ty}")
  val (value, store) = eval(tyProg)
  println(s"========First-Stage Evaluation=========")
  println(s"${pretty.value(value)}")
  (value, store)

private def emitCSource(value: Value, store: Store, cFile: Path, exeFile: Path): Unit =
  assert(value.isInstanceOf[VCode], s"Expected VCode, got ${value.getClass.getSimpleName}")
  val code = CBackend.compileResult((value, store))
  Files.writeString(cFile, code, StandardCharsets.UTF_8)
  println(s"Wrote C code to ${cFile.toAbsolutePath}")
  compileC(cFile, exeFile)
  println(s"Built executable at ${exeFile.toAbsolutePath}")
  println(runExecutable(exeFile))

def cOutputPath(path: Path): Path =
  path.resolveSibling(replaceExtension(path.getFileName.toString, "c"))

def executableOutputPath(path: Path): Path =
  path.resolveSibling(replaceExtension(path.getFileName.toString, "out"))

def inlineCOutputPath: Path = Path.of("instar_inline.c").toAbsolutePath

def inlineExecutableOutputPath: Path = Path.of("instar_inline.out").toAbsolutePath

def compileC(cFile: Path, exeFile: Path): Unit =
  val compileLog = new StringBuilder
  val exitCode =
    Process(Seq("cc", "-std=c11", cFile.toString, "-o", exeFile.toString))
      .!(ProcessLogger(line => compileLog.append(line).append('\n')))
  if exitCode != 0 then throw RuntimeException(s"C compiler exited with code $exitCode")

def runExecutable(exeFile: Path): String =
  Process(Seq(exeFile.toString)).!!.trim

private def replaceExtension(fileName: String, newExt: String): String =
  val dot = fileName.lastIndexOf('.')
  if dot > 0 then s"${fileName.substring(0, dot)}.$newExt"
  else s"$fileName.$newExt"

private def parseArgs(args: List[String]): Unit =
  Config.resetCliState()

  def invalid(message: String): Nothing =
    Config.resetCliState()
    throw IllegalArgumentException(message)

  def loop(rest: List[String]): Unit =
    rest match
      case Nil => ()
      case "--no-elab" :: tail =>
        Config.elab = false
        loop(tail)
      case "--emit-c" :: tail =>
        Config.emitC = true
        loop(tail)
      case ("--program" | "-e") :: src :: tail =>
        if Config.sourceFile.nonEmpty then
          invalid("Pass either a source file or `--program`, not both.\n" + usage)
        else if Config.program.nonEmpty then
          invalid("`--program` was provided more than once.\n" + usage)
        else
          Config.program = Some(src)
          loop(tail)
      case ("--brackets" | "-b") :: tail =>
        Config.brackets = true
        loop(tail)
      case flag :: _ if flag.startsWith("-") =>
        invalid(s"Unknown option `$flag`.\n$usage")
      case path :: tail =>
        if Config.program.nonEmpty then
          invalid("Pass either a source file or `--program`, not both.\n" + usage)
        else if Config.sourceFile.nonEmpty then
          invalid("Pass exactly one source file.\n" + usage)
        else
          Config.sourceFile = Some(Path.of(path))
          loop(tail)

  loop(args)
  (Config.sourceFile, Config.program) match
    case (Some(_), None) => ()
    case (None, Some(_)) => ()
    case _ => invalid(usage)

private val usage =
  "Usage: Main [--emit-c] <source-file>\n" +
    "   or: Main [--emit-c] --program <source>\n" +
    "   or: Main [--emit-c] -e <source>"
