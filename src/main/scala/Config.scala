package instar

import java.nio.file.Path

object Config:
  var emitC: Boolean = false
  var sourceFile: Option[Path] = None
  var program: Option[String] = None
  // Enables inferring of stage application arguments
  var inferStApp: Boolean = false

  def resetCliState(): Unit =
    emitC = false
    sourceFile = None
    program = None
    inferStApp = false
