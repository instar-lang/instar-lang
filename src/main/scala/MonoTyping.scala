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
  import core.Type.*
  import core.{Top, Bot}

  def check(Γ: Env, expr: core.Expr): Unit =
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

  def check(expr: core.Expr): Unit =
    if (expr.eff.get == Top)
      val TCode(_) = expr.ty.get
    check(Map.empty, expr)

/* TODO: bidirectional type checking and elaboration for surface language.
1. use a simpler type definition? Because we don't need to distinguish code fragment and code anymore in the surface language.
2. add subsumption-rule for code type.
3. elaboration respects the subsumption-rule by lift-inserting.
 */
object Elab:
  type Env = Map[String, core.Type]

  def infer(Γ: Env, expr: Expr): core.Expr =
    import core.SubTyping.*
    expr match
      case Expr.EUnit =>
        core.Expr.EUnit.withType(core.Type.TUnit)
      case Expr.ENum(i) =>
        core.Expr.ENum(i).withType(core.Type.TInt)
      case Expr.EBool(b) =>
        core.Expr.EBool(b).withType(core.Type.TBool)
      case Expr.EVar(name) =>
        core.Expr.EVar(name).withType(Γ(name))
      case Expr.ELam(x, argTy, body, retTy) =>
        (argTy, retTy) match
          case (Some(argTy), Some(retTy)) =>
            // Γ, x: argTy ⊢ body ⇐ retTy
            // -----------------------------
            // Γ ⊢ λx: argTy. body: retTy ⇒ argTy → retTy
            val bodyTyped = check(Γ + (x -> argTy), body, retTy)
            core.Expr
              .ELam(x, bodyTyped)
              .withType(core.Type.TFun(argTy, retTy, core.Bot))
          case (Some(argTy), None) =>
            // Γ, x: argTy ⊢ body ⇒ retTy
            // -----------------------------
            // Γ ⊢ λx: argTy. body ⇒ argTy → retTy
            val bodyTyped = infer(Γ + (x -> argTy), body)
            val retTy = bodyTyped.ty.get
            core.Expr
              .ELam(x, bodyTyped)
              .withType(core.Type.TFun(argTy, retTy, core.Bot))
      case Expr.EApp(e1, e2) =>
        val e1Typed = infer(Γ, e1)
        e1Typed.ty.get match
          case core.Type.TCode(core.Type.TFun(argTy, retTy, _)) =>
            // Γ ⊢ e1 ⇒ Code[argTy → retTy]
            // Γ ⊢ e2 ⇐ Code[argTy]
            // ------------------------
            // Γ ⊢ e1 e2 ⇒ Code[retTy]
            val e2Typed = check(Γ, e2, core.Type.TCode(argTy))
            core.Expr
              .EApp(e1Typed, e2Typed, core.Dyn)
              .withType(core.Type.TCode(retTy))
          case core.Type.TFun(argTy, retTy, _) =>
            // Γ ⊢ e1 ⇒ argTy → retTy
            // Γ ⊢ e2 ⇐ argTy
            // ------------------------
            // Γ ⊢ e1 e2 ⇒ retTy
            val e2Typed = check(Γ, e2, argTy)
            core.Expr.EApp(e1Typed, e2Typed, core.Sta).withType(retTy)
      case Expr.ELift(t) =>
        // Γ ⊢ t ⇒ ty
        // ------------------------
        // Γ ⊢ lift t ⇒ Code[ty]
        val tTyped = infer(Γ, t)
        val ty = tTyped.ty.get
        core.Expr.ELift(tTyped).withType(core.Type.TCode(ty))
      case Expr.ERun(t) =>
        // Γ ⊢ t ⇒ Code[ty]
        // ------------------------
        // Γ ⊢ run t ⇒ ty
        val tTyped = infer(Γ, t)
        val core.Type.TCode(ty) = tTyped.ty.get
        core.Expr.ERun(tTyped).withType(ty)
      case Expr.ELet(x, rhs, body) =>
        // Γ ⊢ rhs ⇒ rhsTy
        // Γ, x: rhsTy ⊢ body ⇒ bodyTy
        // -------------------------------
        // Γ ⊢ let x = rhs in body ⇒ bodyTy
        val rhsTyped = infer(Γ, rhs)
        val bodyTyped = infer(Γ + (x -> rhsTyped.ty.get), body)
        core.Expr.ELet(x, rhsTyped, bodyTyped).withType(bodyTyped.ty.get)
      case Expr.ECond(e1, e2, e3) =>
        // We need to infer e1 to know whether it's Bool or Code[Bool] (same as in check)
        val e1Typed = infer(Γ, e1)
        e1Typed.ty.get match
          case core.Type.TBool =>
            // Γ ⊢ e1 ⇒ Bool
            // Γ ⊢ e2 ⇒ ty1
            // Γ ⊢ e3 ⇒ ty2
            // ------------------------
            // Γ ⊢ if e1 then e2 else e3 ⇒ ty1 ⊔ ty2
            val e2Typed = infer(Γ, e2)
            val e3Typed = infer(Γ, e3)
            val join = core.join(e2Typed.ty.get, e3Typed.ty.get)
            // TODO: we need to insert some lifts according to the join type
            core.Expr
              .ECond(
                e1Typed,
                e2Typed,
                e3Typed,
                core.Sta
              )
              .withType(e2Typed.ty.get)
          case core.Type.TCode(core.Type.TBool) =>
            // Γ ⊢ e1 ⇒ Code[Bool]
            // Γ ⊢ e2 ⇒ Code[ty1]
            // Γ ⊢ e3 ⇒ Code[ty2]
            // ------------------------
            // Γ ⊢ if e1 then e2 else e3 ⇒ Code[ty1 ⊔ ty2]

            // The treatment here is weak, because we already know that both
            // branches are code, but we didn't use this information to guide
            // the type checking to insert `lift`s.

            // Can we lift a term of t1 → Code[t2] to Code[t1 → t2]?
            val e2Typed = infer(Γ, e2)
            val e3Typed = infer(Γ, e3)
            val core.Type.TCode(ty1) = e2Typed.ty.get
            val core.Type.TCode(ty2) = e3Typed.ty.get
            val join = core.max(ty1, ty2)
            core.Expr
              .ECond(
                e1Typed,
                e2Typed,
                e3Typed,
                core.Dyn
              )
              .withType(core.Type.TCode(join))
      case Expr.EBinOp(op, e1, e2) =>
        op match
          case "+" | "-" | "*" | "/" =>
            // Γ ⊢ e1 ⇒ ty1
            // Γ ⊢ e2 ⇒ ty2
            // ty1 ⊔ ty2 <: Code[Int]
            // -----------------------
            // Γ ⊢ e1 + e2 ⇒ ty1 ⊔ ty2
            val e1Typed = infer(Γ, e1)
            val e2Typed = infer(Γ, e2)
            val join = core.join(e1Typed.ty.get, e2Typed.ty.get)
            assert(join.subtype(core.Type.TCode(core.Type.TInt)))
            // TODO: insert some lifts according to the join type
            join match
              case core.Type.TCode(_) =>
                core.Expr
                  .EBinOp(op, e1Typed, e2Typed, core.Dyn)
                  .withType(join)
              case _ =>
                core.Expr
                  .EBinOp(op, e1Typed, e2Typed, core.Sta)
                  .withType(join)
          case "==" | "!=" | "<" | "<=" | ">" | ">=" =>
            // Γ ⊢ e1 ⇒ ty1
            // Γ ⊢ e2 ⇒ ty2
            // ty1 ⊔ ty2 <: Code[Int]
            // -----------------------
            // Γ ⊢ e1 == e2 ⇒ ty1 ⊔ ty2
            val e1Typed = infer(Γ, e1)
            val e2Typed = infer(Γ, e2)
            // TODO: insert some lifts according to the join type
            val join = core.join(e1Typed.ty.get, e2Typed.ty.get)
            join match
              case core.Type.TCode(_) =>
                core.Expr
                  .EBinOp(op, e1Typed, e2Typed, core.Dyn)
                  .withType(core.Type.TCode(core.Type.TBool))
              case _ =>
                core.Expr
                  .EBinOp(op, e1Typed, e2Typed, core.Sta)
                  .withType(core.Type.TBool)
      case Expr.EUnaryOp(op, e) =>
        op match
          case "-" =>
            // Γ ⊢ e ⇒ ty
            // ty <: Code[Int]
            // -----------------------
            // Γ ⊢ - e ⇒ ty
            val eTyped = infer(Γ, e)
            val ty = eTyped.ty.get
            assert(ty.subtype(core.Type.TCode(core.Type.TInt)))
            eTyped.ty.get match
              case core.Type.TCode(_) =>
                core.Expr
                  .EUnaryOp(op, eTyped, core.Dyn)
                  .withType(ty)
              case _ =>
                core.Expr
                  .EUnaryOp(op, eTyped, core.Sta)
                  .withType(ty)
      case Expr.EAscribe(e, asTy) =>
        check(Γ, e, asTy)

  def check(Γ: Env, expr: Expr, expected: core.Type): core.Expr =
    import core.SubTyping.*
    expr match
      case Expr.ELam(x, argTy, body, retTy) =>
        expected match
          case core.Type.TFun(argTyExpected, retTyExpected, _) =>
            retTy.map(ty => assert(ty.subtype(retTyExpected)))
            argTy.map(ty => assert(argTyExpected.subtype(ty)))
            // Γ, x: argTy → retTy ⊢ body ⇐ retTyExpected
            // -----------------------------
            // Γ ⊢ λx: argTy. body: retTy ⇐ argTyExpected → retTyExpected
            val bodyTyped = check(Γ + (x -> argTyExpected), body, retTyExpected)
            core.Expr
              .ELam(x, bodyTyped)
              .withType(expected)
      case Expr.EApp(e1, e2) =>
        // Γ ⊢ e1 → argTy → retTy
        // Γ ⊢ e2 ⇐ argTy
        // retTy <: expected
        // ------------------------
        // Γ ⊢ e1 e2 ⇐ expected

        // TODO (DZ): I think it's could be possible to do η-expansion here if
        // e1's type is Code[argTy → retTy], but let's not do it for now.
        val e1Typed = infer(Γ, e1)
        val core.Type.TFun(argTy, retTy, _) = e1Typed.ty.get
        val e2Typed = check(Γ, e2, argTy)
        assert(retTy.subtype(expected))
        expected match
          case core.Type.TCode(_) =>
            core.Expr
              .EApp(e1Typed, e2Typed, core.Dyn)
              .withType(expected)
          case _ =>
            core.Expr
              .EApp(e1Typed, e2Typed, core.Sta)
              .withType(expected)
      case Expr.ELift(t) =>
        // This is a introduction rule for TCode type, the conclusion is the principal judgement.
        // Γ ⊢ t ⇐ ty
        // ------------------------
        // Γ ⊢ lift t ⇐ Code[ty] (principal type)
        val core.Type.TCode(ty) = expected
        check(Γ, t, ty)
      case Expr.ERun(t) =>
        // Elimination rule for TCode type.
        // Γ ⊢ t ⇐ Code[ty]
        // ------------------------
        // Γ ⊢ run t ⇐ ty
        val tTyped = check(Γ, t, core.Type.TCode(expected))
        core.Expr.ERun(tTyped).withType(expected)
      case Expr.ELet(x, rhs, body) =>
        // Γ ⊢ rhs ⇒ ty
        // Γ, x: ty ⊢ body ⇐ expected
        // -------------------------------
        // Γ ⊢ let x = rhs in body ⇐ expected
        val rhsTyped = infer(Γ, rhs)
        val bodyTyped = check(Γ + (x -> rhsTyped.ty.get), body, expected)
        core.Expr.ELet(x, rhsTyped, bodyTyped).withType(expected)
      case Expr.ECond(e1, e2, e3) =>
        // This is an elimination rule for Bool or Code[Bool]

        // we need to infer e1, because we don't know whether it's Bool or Code[Bool]
        val e1Typed = infer(Γ, e1)
        e1Typed.ty.get match
          case core.Type.TBool =>
            // Γ ⊢ e1 ⇒ Bool
            // Γ ⊢ e2 ⇐ expected
            // Γ ⊢ e3 ⇐ expected
            // ------------------------
            // Γ ⊢ if e1 then e2 else e3 ⇐ expected
            val e2Typed = check(Γ, e2, expected)
            val e3Typed = check(Γ, e3, expected)
            core.Expr
              .ECond(e1Typed, e2Typed, e3Typed, core.Sta)
              .withType(expected)
          case core.Type.TCode(core.Type.TBool) =>
            // Γ ⊢ e1 ⇒ Code[Bool]
            // Γ ⊢ e2 ⇐ expected
            // Γ ⊢ e3 ⇐ expected
            // ------------------------
            // Γ ⊢ if e1 then e2 else e3 ⇐ expected

            // expected must be a code type
            assert(expected.isInstanceOf[core.Type.TCode])

            val e2Typed = check(Γ, e2, expected)
            val e3Typed = check(Γ, e3, expected)
            core.Expr
              .ECond(e1Typed, e2Typed, e3Typed, core.Dyn)
              .withType(expected)
      case Expr.EBinOp(op, e1, e2) =>
        op match
          case "+" | "-" | "*" | "/" =>
            // expected <: Code[Int]
            // Γ ⊢ e1 ⇐ expected
            // Γ ⊢ e2 ⇐ expected
            // -----------------------
            // Γ ⊢ e1 + e2 ⇐ expected
            assert(expected.subtype(core.Type.TCode(core.Type.TInt)))
            val e1Typed = check(Γ, e1, expected)
            val e2Typed = check(Γ, e2, expected)
            expected match
              case core.Type.TCode(_) =>
                core.Expr
                  .EBinOp(op, e1Typed, e2Typed, core.Dyn)
                  .withType(expected)
              case _ =>
                core.Expr
                  .EBinOp(op, e1Typed, e2Typed, core.Sta)
                  .withType(expected)
          case "==" | "!=" | "<" | "<=" | ">" | ">=" =>
            // expected <: Code[Bool]
            // Γ ⊢ e1 ⇐ f(expected)
            // Γ ⊢ e2 ⇐ f(expected)
            // where f(Code[T]) = Code[Int]
            //       f(T) = Int
            // -----------------------
            // Γ ⊢ e1 == e2 ⇐ expected
            assert(expected.subtype(core.Type.TCode(core.Type.TBool)))
            def f(t: core.Type) = expected match
              case core.Type.TCode(_) => core.Type.TCode(core.Type.TInt)
              case _                  => core.Type.TInt

            val e1Typed = check(Γ, e1, f(expected))
            val e2Typed = check(Γ, e2, f(expected))
            core.Expr
              .EBinOp(
                op,
                e1Typed,
                e2Typed,
                expected match
                  case core.Type.TCode(_) => core.Dyn
                  case _                  => core.Sta
              )
              .withType(expected)
      case Expr.EUnaryOp(op, e) =>
        op match
          case "-" =>
            // expected <: Code[Int]
            // Γ ⊢ e ⇐ expected
            // -----------------------
            // Γ ⊢ - e ⇐ expected
            assert(expected.subtype(core.Type.TCode(core.Type.TInt)))
        val eTyped = check(Γ, e, expected)
        expected match
          case core.Type.TCode(_) =>
            core.Expr
              .EUnaryOp(op, eTyped, core.Dyn)
              .withType(expected)
          case _ =>
            core.Expr
              .EUnaryOp(op, eTyped, core.Sta)
              .withType(expected)

      case Expr.EAscribe(e, asTy) =>
        // Γ ⊢ expr ⇐ asTy
        // asTy <: expected
        // -----------------------
        // Γ ⊢ (expr: asTy) ⇐ expected
        val typed = check(Γ, e, asTy)
        assert(typed.ty.get.subtype(expected))
        typed.withType(expected)
      case Expr.EUnit | Expr.ENum(_) | Expr.EBool(_) | Expr.EVar(_) =>
        // Apply the change direction rule for these primitive expressions.
        // According to the bidirectional recipe, we should change direction as
        // late as possible so the information of expected type can be preserved
        // more.
        // Γ ⊢ expr ⇒ ty
        // ty <: expected
        // -----------------------
        // Γ ⊢ expr ⇐ expected
        val typed = infer(Γ, expr)
        assert(typed.ty.get.subtype(expected))
        typed
