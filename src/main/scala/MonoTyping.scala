package spmp.tyck.mono

import spmp.core.mono as core
import spmp.surf.mono.*

/*
TODO: type checking for fully annotated core language.
* add effect labels to track code generation side effect.
* add two mutually typing judgements, top-level judgment Γ ⊢ e : τ | ϵ and binding-time sensitive judgment Γ ⊢ˢ e : τ | ϵ.
* add binding-time wellformedness restrictions.
*/
/*
Note: there is a gap between MonoCore and Core.
*/
object Tyck:
  type Env = Map[String, (core.Stage, core.Type)]

  def check(expr: core.Expr): Unit =
    ???

/*
TODO: bidirectional type checking and elaboration for surface language.
1. use a simpler type definition? Because we don't need to distinguish code fragment and code anymore in the surface language.
*/
object Elab:
  type Env = Map[String, core.Type]

  def infer(env: Env, stage: core.Stage, expr: Expr): core.Expr =
    ???

  def check(env: Env, stage: core.Stage, expr: Expr, expected: core.Type): core.Expr =
    ???