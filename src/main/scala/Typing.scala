package spmp.tyck

import spmp.eff as core
import spmp.eff.Type
import spmp.eff.Stage

import spmp.surf.*
import spmp.Counter.fresh

type Env = Map[String, core.Type]
type StEnv = Set[String]

object Subtyping:
  extension (t1: Type)
    // Subtyping relation: t1 <: t2
    def subtype(t2: Type, stenv: StEnv): Boolean = (t1, t2) match
      case (
            Type.TFun(arg1, ret1),
            Type.TCode(Type.TFun(arg2, ret2))
          ) =>
        Type.TCode(arg2).subtype(arg1, stenv) && ret1.subtype(
          Type.TCode(ret2),
          stenv
        )
      case (Type.TFun(arg1, ret1), Type.TFun(arg2, ret2)) =>
        // contravariant in argument, covariant in return
        arg2.subtype(arg1, stenv) && ret1.subtype(ret2, stenv)
      case (Type.TCode(t1), Type.TCode(t2)) => // Code[t1] <: Code[t2]
        t1.subtype(t2, stenv)
      case (Type.TBool, Type.TCode(Type.TBool)) |
          (Type.TUnit, Type.TCode(Type.TUnit)) |
          (Type.TInt, Type.TCode(Type.TInt)) =>
        // bool <: Code[bool]
        // unit <: Code[unit]
        // int  <: Code[int]
        true
      case (Type.TBool | Type.TUnit | Type.TInt, Type.TAt(t, Stage.SVar(s)))
          if t == t1 =>
        //     s ∈ Γ
        // ---------------
        // int <: int@s

        //     s ∈ Γ
        // ---------------
        // bool <: bool@s

        //     s ∈ Γ
        // ---------------
        // unit <: unit@s
        stenv.contains(s)
      case (
            Type.TFun(arg1, ret1),
            Type.TAt(Type.TFun(arg2, ret2), Stage.SVar(s))
          ) =>
        // s ∈ Γ    arg2@s <: arg1   ret1 <: ret2@s
        // ----------------------------------------
        //     arg1 -> ret1 <: (arg2 -> ret2)@s
        stenv.contains(s)
        && Type.TAt(arg2, Stage.SVar(s)).subtype(arg1, stenv)
        && ret1.subtype(Type.TAt(ret2, Stage.SVar(s)), stenv)
      case (Type.TForallSt(s1, t1), Type.TForallSt(s2, t2)) =>
        // Γ, s ⊢ t1 <: t2
        // -----------------------
        // ∀s.t1 <: ∀s.t2
        val sFresh = fresh(prefix = "s")
        val t1Inst = t1.subst(s1, Stage.SVar(sFresh))
        val t2Inst = t2.subst(s2, Stage.SVar(sFresh))
        t1Inst.subtype(t2Inst, stenv + sFresh)
      case (a, b) =>
        a == b // TODO: Make where this case (reflexivity) is applied more explicit

    def subst(s: String, st: Stage): Type = t1 match
      case Type.TUnit | Type.TInt | Type.TBool => t1
      case Type.TFun(t1a, t1r) =>
        Type.TFun(t1a.subst(s, st), t1r.subst(s, st))
      case Type.TForallSt(s1, t) =>
        if s1 == s then t1
        else Type.TForallSt(s1, t.subst(s, st))
      case Type.TAt(t, Stage.SVar(s1)) =>
        if s1 == s then Type.TAt(t, st)
        else Type.TAt(t.subst(s, st), Stage.SVar(s1))
      case Type.TAt(t, st) =>
        Type.TAt(t.subst(s, st), st)
      case Type.TCode(t) =>
        Type.TCode(t.subst(s, st))

    def join(t2: Type, stenv: StEnv): Type =
      import Subtyping.*
      // we require t1 <: t2 or t2 <: t1 when calling ⊔
      if t1.subtype(t2, stenv) then t2
      else if t2.subtype(t1, stenv) then t1
      else
        val str = stenv.mkString("{ ", ", ", " }")
        // no join type
        throw new Exception(
          s"$t1 and $t2 is not comparable under $str (neither t1 <: t2 nor t2 <: t1)"
        )

def infer(env: Env, stenv: StEnv, expr: Expr): core.Expr =
  import Subtyping.*
  expr match
    case Expr.EUnit =>
      core.Expr.EUnit.withType(Type.TUnit)
    case Expr.ENatV(n) =>
      core.Expr.ENum(n).withType(Type.TInt)
    case Expr.EVar(x) =>
      core.Expr.EVar(x).withType(env(x))
    case Expr.ELam(x, ty, body) =>
      // Γ, x: argTy ⊢ body ⇐ retTy
      // -------------------------------------------
      // Γ ⊢ λx: argTy. body: retTy ⇒ argTy → retTy
      val bodyTyped = infer(env + (x -> ty), stenv, body)
      core.Expr
        .ELam(x, Some(ty), bodyTyped, bodyTyped.ty)
        .withType(
          Type.TFun(ty, bodyTyped.ty.get)
        )
    case Expr.ESLam(s, body) =>
      // Γ, s ⊢ body ⇒ ty
      // ---------------------------
      // Γ ⊢ Λs. body ⇒ ∀s. ty
      val bodyTyped = infer(env, stenv + s, body)
      core.Expr
        .ESLam(s, bodyTyped)
        .withType(
          Type.TForallSt(s, bodyTyped.ty.get)
        )
    case Expr.ELet(x, rhs, body) =>
      val rhsTyped = infer(env, stenv, rhs)
      val bodyTyped = infer(env + (x -> rhsTyped.ty.get), stenv, body)
      core.Expr.ELet(x, rhsTyped, bodyTyped).withType(bodyTyped.ty.get)
    case Expr.ELift(e) =>
      val eTyped = infer(env, stenv, e)
      eTyped.ty.get match
        case Type.TInt | Type.TBool | Type.TUnit =>
          core.Expr
            .ELift(eTyped, core.Sta)
            .withType(
              Type.TCode(eTyped.ty.get)
            )
        case Type.TFun(Type.TCode(argTy), Type.TCode(retTy)) =>
          core.Expr
            .ELift(eTyped, core.Dyn)
            .withType(
              Type.TCode(Type.TFun(argTy, retTy))
            )
    case Expr.ERun(e) =>
      val eTyped = infer(env, stenv, e)
      core.Expr.ERun(eTyped).withType(eTyped.ty.get)
    case Expr.EApp(e1, e2) =>
      val e1Typed = infer(env, stenv, e1)
      e1Typed.ty.get match
        case Type.TFun(argTy, retTy) =>
          val e2Typed = check(env, stenv, e2, argTy)
          core.Expr.EApp(e1Typed, e2Typed, core.Sta).withType(retTy)
        case Type.TCode(Type.TFun(argTy, retTy)) =>
          val e2Typed = check(env, stenv, e2, Type.TCode(argTy))
          core.Expr.EApp(e1Typed, e2Typed, core.Dyn).withType(Type.TCode(retTy))
    case Expr.ESApp(e, s) =>
      // Γ ⊢ e ⇒ ∀s1. ty
      // --------------------
      // Γ ⊢ e [s] ⇒ ty[s/s1]
      val eTyped = infer(env, stenv, e)
      val Type.TForallSt(s1, ty) = eTyped.ty.get
      val inst = ty.subst(s1, s)
      core.Expr.ESApp(eTyped, s).withType(inst)
    case Expr.EFix(f, ty, e) =>
      ???
    case Expr.EIfz(cond, thn, els) =>
      val condTyped = infer(env, stenv, cond)
      condTyped.ty.get match
        case Type.TInt =>
          // Γ ⊢ cond ⇒ Int
          // Γ ⊢ thn ⇒ ty1
          // Γ ⊢ els ⇒ ty2
          // ty1 ⊔ ty2 = ty
          // -----------------------------------
          // Γ ⊢ ifz cond then thn else els ⇒ ty
          val thnTyped = infer(env, stenv, thn)
          val elsTyped = infer(env, stenv, els)
          val joined = thnTyped.ty.get.join(elsTyped.ty.get, stenv)
          core.Expr
            .ECond(
              core.Expr.EBinOp("==", condTyped, core.Expr.ENum(0), core.Sta),
              thnTyped,
              elsTyped,
              core.Sta
            )
            .withType(joined)
        case Type.TCode(Type.TInt) =>
          // Γ ⊢ cond ⇒ Code[Int]
          // Γ ⊢ thn ⇒ ty1
          // Γ ⊢ els ⇒ ty2
          // ty1 ⊔ ty2 = Code[_]
          // ------------------------------------------
          // Γ ⊢ ifz cond then thn else els ⇒ ty1 ⊔ ty2
          val thnTyped = infer(env, stenv, thn)
          val elsTyped = infer(env, stenv, els)
          val joined = thnTyped.ty.get.join(elsTyped.ty.get, stenv)
          assert(joined.isInstanceOf[Type.TCode])
          core.Expr
            .ECond(
              core.Expr.EBinOp("==", condTyped, core.Expr.ENum(0), core.Dyn),
              thnTyped,
              elsTyped,
              core.Dyn
            )
            .withType(joined)
        case Type.TAt(Type.TInt, s) =>
          // Γ ⊢ cond ⇒ Int@s
          // Γ ⊢ thn ⇒ ty1
          // Γ ⊢ els ⇒ ty2
          // ty1 ⊔ ty2 = _@s
          // -----------------------------------
          // Γ ⊢ ifz cond then thn else els ⇒ ty1 ⊔ ty2
          val thnTyped = infer(env, stenv, thn)
          val elsTyped = infer(env, stenv, els)
          val joined = thnTyped.ty.get.join(elsTyped.ty.get, stenv)
          assert(joined match
            case Type.TAt(_, s1) if s1 == s => true
            case _                          => false
          )
          core.Expr
            .ECond(
              core.Expr.EBinOp("==", condTyped, core.Expr.ENum(0), s),
              thnTyped,
              elsTyped,
              s
            )
            .withType(joined)
    case Expr.EIf(_, _, _) => ???
    case Expr.EBin(op, left, right) =>
      op match
        case "+" | "-" | "*" | "/" =>
          // Γ ⊢ e1 ⇒ ty1
          // Γ ⊢ e2 ⇒ ty2
          // ty1 ⊔ ty2 <: Code[Int] or ty1 ⊔ ty2 = Int@s
          // -------------------------------------------
          // Γ ⊢ e1 + e2 ⇒ ty1 ⊔ ty2
          val leftTyped = infer(env, stenv, left)
          val rightTyped = infer(env, stenv, right)
          val joined = leftTyped.ty.get.join(rightTyped.ty.get, stenv)
          // Now we dont have int@s <: Code[int], so we have this hack: ty1 ⊔ ty2 = Int@s
          // TODO: try to remove this hack (mabe we can check erase(ty1 ⊔ ty2) <: Int)
          val isIntAtS = joined match
            case Type.TAt(Type.TInt, Stage.SVar(_)) => true
            case _                                  => false
          assert(joined.subtype(Type.TCode(Type.TInt), stenv) || isIntAtS)
          val stage = joined match
            case Type.TCode(_)          => core.Dyn
            case Type.TAt(Type.TInt, s) => s
            case _                      => core.Sta
          core.Expr
            .EBinOp(op, leftTyped, rightTyped, stage)
            .withType(joined)
        case "==" | "!=" | "<" | "<=" | ">" | ">=" =>
          // Γ ⊢ e1 ⇒ ty1
          // Γ ⊢ e2 ⇒ ty2
          // ty1 ⊔ ty2 <: Code[Int] or ty1 ⊔ ty2 = Int@s
          // ---------------------------------------------------------------------------------------
          // Γ ⊢ e1 == e2 ⇒ f(ty1 ⊔ ty2) where f(Code[t]) = Code[Bool], f(t@s) = Bool@s, f(t) = Bool
          val leftTyped = infer(env, stenv, left)
          val rightTyped = infer(env, stenv, right)
          val joined = leftTyped.ty.get.join(rightTyped.ty.get, stenv)
          val isIntAtS = joined match
            case Type.TAt(Type.TInt, Stage.SVar(_)) => true
            case _                                  => false
          // Now we dont have int@s <: Code[int], so we have this hack: ty1 ⊔ ty2 = Int@s
          // TODO: try to remove this hack
          assert(
            joined.subtype(Type.TCode(Type.TInt), stenv) || isIntAtS
          )
          def f(t: Type): Type = t match
            case Type.TCode(_)  => Type.TCode(Type.TBool)
            case Type.TAt(_, s) => Type.TAt(Type.TBool, s)
            case _              => Type.TBool
          val retType = f(joined)
          val stage = joined match
            case Type.TCode(_)          => core.Dyn
            case Type.TAt(Type.TInt, s) => s
            case _                      => core.Sta
          core.Expr
            .EBinOp(op, leftTyped, rightTyped, stage)
            .withType(retType)
    case Expr.EAlloc(e)       => ???
    case Expr.EGet(e)         => ???
    case Expr.EPut(e1, e2)    => ???
    case Expr.EAscribe(e, ty) =>
      // Γ ⊢ e ⇐ ty
      // -----------------
      // Γ ⊢ (e : ty) ⇒ ty
      val eTyped = infer(env, stenv, e)
      assert(eTyped.ty.get == ty)
      eTyped.withType(ty)

def check(env: Env, stenv: StEnv, expr: Expr, expected: Type): core.Expr =
  import Subtyping.*
  expr match
    case Expr.ESLam(s, body) =>
      // Γ, s ⊢ body ⇐ ty
      // expected = ∀s. ty
      // ---------------------------------------
      // Γ ⊢ Λs. body ⇐ ∀s. ty
      val Type.TForallSt(s1, ty) = expected
      val inst = ty.subst(s1, Stage.SVar(s))
      val bodyTyped = check(env, stenv + s, body, inst)
      core.Expr.ESLam(s, bodyTyped).withType(expected)
    case Expr.ELet(x, rhs, body) =>
      // Γ ⊢ rhs ⇒ ty
      // Γ, x: ty ⊢ body ⇐ expected
      // -------------------------------
      // Γ ⊢ let x = rhs in body ⇐ expected
      val rhsTyped = infer(env, stenv, rhs)
      val bodyTyped = check(env + (x -> rhsTyped.ty.get), stenv, body, expected)
      core.Expr.ELet(x, rhsTyped, bodyTyped).withType(bodyTyped.ty.get)
    case Expr.ELift(e) =>
      expected match
        case Type.TCode(Type.TInt) | Type.TCode(Type.TBool) |
            Type.TCode(Type.TUnit) =>
          // Γ ⊢ e ⇐ Int
          // --------------------------------
          // Γ ⊢ lift e ⇐ Code[Int]
          val eTyped = check(
            env,
            stenv,
            e,
            expected match
              case Type.TCode(Type.TInt)  => Type.TInt
              case Type.TCode(Type.TBool) => Type.TBool
              case Type.TCode(Type.TUnit) => Type.TUnit
          )
          core.Expr.ELift(eTyped, core.Sta).withType(expected)
        case Type.TCode(Type.TFun(argTy, retTy)) =>
          // Γ ⊢ e ⇐ Code[argTy] -> Code[retTy]
          // ----------------------------------------
          // Γ ⊢ lift e ⇐ Code[argTy -> retTy]
          val eTyped = check(
            env,
            stenv,
            e,
            Type.TFun(Type.TCode(argTy), Type.TCode(retTy))
          )
          core.Expr.ELift(eTyped, core.Dyn).withType(expected)
    case Expr.ERun(e) =>
      // Γ ⊢ e ⇐ Code[ty]
      // ------------------------
      // Γ ⊢ run e ⇐ ty
      val eTyped = check(env, stenv, e, Type.TCode(expected))
      core.Expr.ERun(eTyped).withType(expected)
    case Expr.EIfz(cond, thn, els) =>
      val condTyped = infer(env, stenv, cond)
      condTyped.ty.get match
        case Type.TInt =>
          // Γ ⊢ cond ⇒ Int
          // Γ ⊢ thn ⇐ expected
          // Γ ⊢ els ⇐ expected
          // -------------------------------------------------------
          // Γ ⊢ ifz cond then thn else els ⇐ expected
          val thnTyped = check(env, stenv, thn, expected)
          val elsTyped = check(env, stenv, els, expected)
          core.Expr
            .ECond(
              core.Expr.EBinOp("==", condTyped, core.Expr.ENum(0), core.Sta),
              thnTyped,
              elsTyped,
              core.Sta
            )
            .withType(expected)
        case Type.TCode(Type.TInt) =>
          // Γ ⊢ cond ⇒ Code[Int]
          // Γ ⊢ thn ⇐ expected
          // Γ ⊢ els ⇐ expected
          // -------------------------------------------------------
          // Γ ⊢ ifz cond then thn else els ⇐ expected
          val thnTyped = check(env, stenv, thn, expected)
          val elsTyped = check(env, stenv, els, expected)
          core.Expr
            .ECond(
              core.Expr.EBinOp("==", condTyped, core.Expr.ENum(0), core.Dyn),
              thnTyped,
              elsTyped,
              core.Dyn
            )
            .withType(expected)
    case Expr.EIf(cond, thn, els) =>
      val condTyped = infer(env, stenv, cond)
      condTyped.ty.get match
        case Type.TBool =>
          // Γ ⊢ cond ⇒ Bool
          // Γ ⊢ thn ⇐ expected
          // Γ ⊢ els ⇐ expected
          // ----------------------------------------
          // Γ ⊢ if cond then thn else els ⇐ expected
          val thnTyped = check(env, stenv, thn, expected)
          val elsTyped = check(env, stenv, els, expected)
          core.Expr
            .ECond(condTyped, thnTyped, elsTyped, core.Sta)
            .withType(expected)
        case Type.TCode(Type.TBool) =>
          // Γ ⊢ cond ⇒ Code[Bool]
          // Γ ⊢ thn ⇐ expected
          // Γ ⊢ els ⇐ expected
          // expected is Code[_]
          // ----------------------------------------
          // Γ ⊢ if cond then thn else els ⇐ expected
          assert(expected.isInstanceOf[Type.TCode])

          val thnTyped = check(env, stenv, thn, expected)
          val elsTyped = check(env, stenv, els, expected)
          core.Expr
            .ECond(condTyped, thnTyped, elsTyped, core.Dyn)
            .withType(expected)
    case Expr.EBin(op, left, right) =>
      op match
        case "+" | "-" | "*" | "/" =>
          // expected <: Code[Int]
          // Γ ⊢ left ⇐ expected
          // Γ ⊢ right ⇐ expected
          // ----------------------------
          // Γ ⊢ left ⊕ right ⇐ expected
          assert(expected.subtype(Type.TCode(Type.TInt), stenv))
          val leftTyped = check(env, stenv, left, expected)
          val rightTyped = check(env, stenv, right, expected)
          val stage = expected match
            case Type.TCode(_) => core.Dyn
            case _             => core.Sta
          core.Expr
            .EBinOp(op, leftTyped, rightTyped, stage)
            .withType(expected)
        case "==" | "!=" | "<" | "<=" | ">" | ">=" =>
          // expected <: Code[Bool]
          // Γ ⊢ left ⇐ f(expected)
          // Γ ⊢ right ⇐ f(expected)
          // where f(Code[Bool]) = Code[Int], f(Bool) = Int
          // --------------------------------------------
          // Γ ⊢ left == right ⇐ expected
          assert(expected.subtype(Type.TCode(Type.TBool), stenv))
          def f(t: Type): Type = t match
            case Type.TCode(Type.TBool) => Type.TCode(Type.TInt)
            case Type.TBool             => Type.TInt
          val leftTyped = check(env, stenv, left, f(expected))
          val rightTyped = check(env, stenv, right, f(expected))
          val stage = expected match
            case Type.TCode(_) => core.Dyn
            case _             => core.Sta
          core.Expr
            .EBinOp(op, leftTyped, rightTyped, stage)
            .withType(expected)
    case Expr.ESApp(e, s) =>
      // Γ, s ⊢ e ⇐ ty[s/s1]
      // --------------------
      // Γ ⊢ e [s] ⇐ ∀s1. ty
      val Type.TForallSt(s1, ty) = expected
      val inst = ty.subst(s1, s)
      val eTyped = check(env, stenv, e, inst)
      core.Expr.ESApp(eTyped, s).withType(expected)
    case Expr.EFix(f, ty, e)                                             => ???
    case Expr.EAlloc(e)                                                  => ???
    case Expr.EGet(e)                                                    => ???
    case Expr.EPut(e1, e2)                                               => ???
    case Expr.EAscribe(_, _) | Expr.EUnit | Expr.ENatV(_) | Expr.EVar(_) =>
      // Γ ⊢ expr ⇒ ty
      // ty <: expected
      // -----------------------
      // Γ ⊢ expr ⇐ expected
      val exprTyped = infer(env, stenv, expr)
      assert(exprTyped.ty.get.subtype(expected, stenv))
      exprTyped
