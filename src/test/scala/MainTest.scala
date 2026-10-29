package instar

import java.io.ByteArrayOutputStream
import java.io.PrintStream
import java.nio.charset.StandardCharsets
import java.nio.file.Files
import java.nio.file.Path

import munit.FunSuite

class MainTest extends FunSuite:
  private def captureStdout(thunk: => Unit): String =
    val buffer = ByteArrayOutputStream()
    Console.withOut(PrintStream(buffer)) {
      thunk
    }
    buffer.toString(StandardCharsets.UTF_8).trim

  private def deleteIfExists(path: Path): Unit =
    Files.deleteIfExists(path)

  test("main evaluates inline programs via --program") {
    val out = captureStdout {
      main(Array("--program", "let x = 41 in x + 1"))
    }
    assert(out.contains("Some(TInt)"))
    assert(out.contains("42"))
  }

  test("main compiles and runs inline programs via --emit-c --program") {
    val cFile = inlineCOutputPath
    val exeFile = inlineExecutableOutputPath

    try
      deleteIfExists(cFile)
      deleteIfExists(exeFile)

      val out = captureStdout {
        main(Array("--emit-c", "--program", "lift[2](1) +@2 lift[2](2)"))
      }

      assert(Files.exists(cFile))
      assert(Files.exists(exeFile))
      assert(out.contains(s"Wrote C code to ${cFile.toAbsolutePath}"))
      assert(out.contains(s"Built executable at ${exeFile.toAbsolutePath}"))
      assert(out.linesIterator.toList.lastOption.contains("3"))
    finally
      deleteIfExists(cFile)
      deleteIfExists(exeFile)
  }

  test("main compiles and runs inline programs via --program --emit-c") {
    val cFile = inlineCOutputPath
    val exeFile = inlineExecutableOutputPath

    try
      deleteIfExists(cFile)
      deleteIfExists(exeFile)

      val out = captureStdout {
        main(Array("--program", "lift[2](2) +@2 lift[2](3)", "--emit-c"))
      }

      assert(Files.exists(cFile))
      assert(Files.exists(exeFile))
      assert(out.contains(s"Wrote C code to ${cFile.toAbsolutePath}"))
      assert(out.contains(s"Built executable at ${exeFile.toAbsolutePath}"))
      assert(out.linesIterator.toList.lastOption.contains("5"))
    finally
      deleteIfExists(cFile)
      deleteIfExists(exeFile)
  }
