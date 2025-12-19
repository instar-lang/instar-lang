package spmp.tyck.mono

import spmp.core.mono as core
import spmp.surf.mono.*

/* TODO: type checking for fully annotated core language.
1. add effect labels to track code generation side effect.
2. add binding-time wellformedness restrictions.
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

// TODO: extend MonoCore with effect subsumption-rule.
object Tyck:
  type Env = Map[String, core.Type]

  def check(Γ: Env, expr: core.Expr): Unit =
    import core.Type.*
    import core.{Top, Bot}
    expr match
      case core.Expr.EUnit => assert(expr.ty.get == TUnit); assert(expr.eff.get == Bot)
      case core.Expr.ENum(i) => assert(expr.ty.get == TInt); assert(expr.eff.get == Bot)
      case core.Expr.EBool(b) => assert(expr.ty.get == TBool); assert(expr.eff.get == Bot)
      case core.Expr.EVar(x) => assert(expr.ty.get == Γ(x)); assert(expr.eff.get == Bot)
      case core.Expr.ELam(x, body) =>
        val TFun(argTy, retTy, eff) = expr.ty.get
        assert(body.ty.get == retTy)
        assert(body.eff.get == eff); assert(expr.eff.get == Bot)
        check(Γ + (x -> argTy), body)
      case core.Expr.EApp(e1, e2, st) if st == core.Sta =>
        val TFun(argTy, retTy, eff) = e1.ty.get
        assert(e2.ty.get == argTy); assert(expr.ty.get == retTy)
        assert(expr.eff.get == eff || e1.eff.get || e2.eff.get)
        check(Γ, e1); check(Γ, e2)
      case core.Expr.EApp(e1, e2, st) if st == core.Dyn =>
        val TCode(TFun(argTy, retTy, Bot)) = e1.ty.get
        assert(e2.ty.get == TCode(argTy)); assert(expr.ty.get == TCode(retTy))
        assert(expr.eff.get == Top)
        check(Γ, e1); check(Γ, e2)
      case core.Expr.ELift(t) =>
        t.ty.get match
          case TUnit => assert(expr.ty.get == TCode(TUnit))
          case TInt => assert(expr.ty.get == TCode(TInt))
          case TBool => assert(expr.ty.get == TCode(TBool))
          case TFun(t1, t2, _) => assert(expr.ty.get == TCode(TFun(t1, t2, Bot)))
        assert(expr.eff.get == Top)
        check(Γ, t)
      case core.Expr.ERun(t) =>
        val TCode(ty) = t.ty.get
        assert(expr.ty.get == ty)
        assert(expr.eff.get == Bot)
        // Note: check run in an empty context
        check(Map.empty, t)
      case core.Expr.ELet(x, rhs, body) =>
        assert(expr.ty.get == body.ty.get)
        assert(expr.eff.get == rhs.eff.get || body.eff.get)
        check(Γ + (x -> rhs.ty.get), body)
      case core.Expr.ECond(e1, e2, e3, st) if st == core.Sta =>
        val ty = expr.ty.get
        assert(e1.ty.get == TBool); assert(e2.ty.get == ty); assert(e3.ty.get == ty)
        assert(expr.eff.get == e1.eff.get || e2.eff.get || e3.eff.get)
        check(Γ, e1); check(Γ, e2); check(Γ, e3)
      case core.Expr.ECond(e1, e2, e3, st) if st == core.Dyn =>
        val TCode(ty) = expr.ty.get
        assert(e1.ty.get == TCode(TBool)); assert(e2.ty.get == TCode(ty)); assert(e3.ty.get == TCode(ty))
        assert(expr.eff.get == Top)
        check(Γ, e1); check(Γ, e2); check(Γ, e3)
      case core.Expr.EBinOp(op, e1, e2, st) if st == core.Sta =>
        op match
          case "+" | "-" | "*" | "/" =>
            assert(expr.ty.get == TInt); assert(e1.ty.get == TInt); assert(e2.ty.get == TInt)
          case "==" | "!=" | "<" | "<=" | ">" | ">=" =>
            assert(expr.ty.get == TBool); assert(e1.ty.get == TInt); assert(e2.ty.get == TInt)
        assert(expr.eff.get == e1.eff.get || e2.eff.get)
        check(Γ, e1); check(Γ, e2)
      case core.Expr.EBinOp(op, e1, e2, st) if st == core.Dyn =>
        op match
          case "+" | "-" | "*" | "/" =>
            assert(expr.ty.get == TCode(TInt)); assert(e1.ty.get == TCode(TInt)); assert(e2.ty.get == TCode(TInt))
          case "==" | "!=" | "<" | "<=" | ">" | ">=" =>
            assert(expr.ty.get == TCode(TBool)); assert(e1.ty.get == TCode(TInt)); assert(e2.ty.get == TCode(TInt))
        assert(expr.eff.get == Top)
        check(Γ, e1); check(Γ, e2)
      case core.Expr.EUnaryOp(op, e, st) if st == core.Sta =>
        op match
          case "-" =>
            assert(expr.ty.get == TInt); assert(e.ty.get == TInt)
        assert(expr.eff.get == e.eff.get)
        check(Γ, e)
      case core.Expr.EUnaryOp(op, e, st) if st == core.Dyn =>
        op match
          case "-" =>
            assert(expr.ty.get == TCode(TInt)); assert(e.ty.get == TCode(TInt))
        assert(expr.eff.get == Top)
        check(Γ, e)

/* TODO: bidirectional type checking and elaboration for surface language.
1. use a simpler type definition? Because we don't need to distinguish code fragment and code anymore in the surface language.
2. add subsumption-rule for code type.
3. elaboration respects the subsumption-rule by lift-inserting.
*/
object Elab:
  type Env = Map[String, core.Type]

  def infer(Γ: Env, stage: core.Stage, expr: Expr): core.Expr =
    ???

  def check(Γ: Env, stage: core.Stage, expr: Expr, expected: core.Type): core.Expr =
    ???