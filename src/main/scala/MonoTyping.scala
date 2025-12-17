package spmp.tyck.mono

import spmp.core.mono as core
import spmp.surf.mono as surf

/* TODO: type checking for fully annotated core language.
1. add effect labels to track code generation side effect.
2. add two mutually typing judgements,
   top-level judgment Γ ⊢ e : τ | ϵ and
   binding-time sensitive judgment Γ ⊢ˢ e : τ | ϵ.
3. add binding-time wellformedness restrictions.
*/

/* TODO: extend MonoCore with stage polymorphism.
1. if we extend all constructor of MonoCore with stage polymorphism, some typing rules may become ambiguous.

  when s = 1
  Γ; Σ ⊢¹ e₁ : nat | ϵ₁
  Γ; Σ ⊢¹ e₂ : τ | ϵ₂
  Γ; Σ ⊢¹ e₃ : τ | ϵ₃
  ————————————————————————————————————————
  Γ; Σ ⊢¹ ifzˢ e₁ e₂ e₃ : τ | ϵ₁ ⊔ ϵ₂ ⊔ ϵ₃

  when s = 2
  Γ; Σ ⊢¹ e₁ : frag nat | ϵ₁
  Γ; Σ ⊢ e₂ : rep τ | ϵ₂
  Γ; Σ ⊢ e₃ : rep τ | ϵ₃
  ——————————————————————————————————
  Γ; Σ ⊢¹ ifzˢ e₁ e₂ e₃ : frag τ | ⊤

2. we may need to add following interpretations to merge two typing rules above.
  - an interpretation for code fragment `fragˢ` where frag¹ τ = τ and frag² τ = frag τ.
  - an interpretation for code `repˢ` where rep¹ τ = τ and rep² τ = rep τ.
  - an interpretation for effect label `ϵˢ` where ϵ¹ = ⊥ and ϵ² = ⊤.
  - in top-level judgment Γ; Σ ⊢ e : τ | ϵ, the answer type τ must be a rep type when ϵ = ⊤.
  - how can we ensure this when τ and ϵ may depend on some free or bound stage variables?

3. or alternative: remove the effect system,
   but the top-level program is well-formed only under the rep type,
   which means that our two-level programs always generate code.
*/
object Tyck:
  type Env = Map[String, (core.Stage, core.Type)]

  def check(expr: core.Expr): Unit =
    ???


/* TODO: bidirectional type checking and elaboration for surface language.
1. use a simpler type definition? Because we don't need to distinguish code fragment and code anymore in the surface language.
*/
object Elab:
  type Env = Map[String, core.Type]

  def infer(env: Env, stage: core.Stage, expr: surf.Expr): core.Expr =
    ???

  def check(env: Env, stage: core.Stage, expr: surf.Expr, expected: core.Type): core.Expr =
    ???