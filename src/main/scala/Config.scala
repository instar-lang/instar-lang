package instar

import java.nio.file.Path

object Config:
  var emitC: Boolean = false
  var sourceFile: Option[Path] = None
  var program: Option[String] = None
  // Enables type-directed elaborations (e.g. inserting lifts) to make the
  // program well-typed.
  var elab: Boolean = true
  // Enables inferring of stage application arguments
  var inferStApp: Boolean = false
  var brackets: Boolean = false

  def resetCliState(): Unit =
    emitC = false
    sourceFile = None
    program = None
    elab = true
    inferStApp = false
    brackets = false