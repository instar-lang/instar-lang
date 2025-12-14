package spmp.tyck.mono

import spmp.core.mono as core
import spmp.surf.mono.*

// type checking for fully annotated core language.
object Tyck:
  type Env = Map[String, (core.Stage, core.Type)]

  def check(expr: core.Expr): Unit =
    ???

// bidirectional type checking and elaboration for surface language.
object Elab:
  type Env = Map[String, core.Type]

  def infer(env: Env, stage: core.Stage, expr: Expr): core.Expr =
    ???

  def check(env: Env, stage: core.Stage, expr: Expr, expected: core.Type): core.Expr =
    ???