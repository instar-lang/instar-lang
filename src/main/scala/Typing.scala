package spmp.tyck

import spmp.eff as core
import spmp.eff.Type
import spmp.eff.Stage

import spmp.surf.*
import spmp.Counter.fresh
import scala.util.{Try, Success, Failure}

type Env = Map[String, core.Type]

enum StEnvElem:
  case SVar(s: String)
  case ExistSVar(s: String)
  case ExistSVarBound(s: String, bound: Stage)

type StEnv = List[StEnvElem]

val EmptyStEnv: StEnv = List.empty

extension (stenv: StEnv)
  def containsSVar(s: String): Boolean =
    stenv.exists {
      case StEnvElem.SVar(s1)              => s1 == s
      case StEnvElem.ExistSVar(s1)         => false
      case StEnvElem.ExistSVarBound(s1, _) => false
    }

  def addSVar(s: String): StEnv =
    StEnvElem.SVar(s) :: stenv

  def addExistSVar(s: String): StEnv =
    StEnvElem.ExistSVar(s) :: stenv

object Subtyping:

  case class SubtypeError(message: String) extends Exception(message)

  extension (t1: Type)
    // Subtyping relation: t1 <: t2
    def subtype(t2: Type, stenv: StEnv): StEnv = (t1, t2) match
      case (
            Type.TFun(arg1, ret1),
            Type.TCode(Type.TFun(arg2, ret2))
          ) =>
        val stenv1 = Type.TCode(arg2).subtype(arg1, stenv)
        ret1.subtype(
          Type.TCode(ret2),
          stenv1
        )
      case (Type.TFun(arg1, ret1), Type.TFun(arg2, ret2)) =>
        // contravariant in argument, covariant in return
        val stenv1 = arg2.subtype(arg1, stenv)
        ret1.subtype(ret2, stenv1)
      case (Type.TCode(t1), Type.TCode(t2)) =>
        // Code[t1] <: Code[t2]
        t1.subtype(t2, stenv)
      case (Type.TBool, Type.TCode(Type.TBool)) |
          (Type.TUnit, Type.TCode(Type.TUnit)) |
          (Type.TInt, Type.TCode(Type.TInt)) =>
        // bool <: Code[bool]
        // unit <: Code[unit]
        // int  <: Code[int]
        stenv
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
        assert(stenv.containsSVar(s))
        stenv
      case (
            Type.TFun(arg1, ret1),
            Type.TAt(Type.TFun(arg2, ret2), Stage.SVar(s))
          ) =>
        // s ∈ Γ    arg2@s <: arg1   ret1 <: ret2@s
        // ----------------------------------------
        //     arg1 -> ret1 <: (arg2 -> ret2)@s
        assert(stenv.containsSVar(s))
        val stenv1 = Type.TAt(arg2, Stage.SVar(s)).subtype(arg1, stenv)
        ret1.subtype(Type.TAt(ret2, Stage.SVar(s)), stenv1)
      case (Type.TForallSt(s1, t1), Type.TForallSt(s2, t2)) =>
        // Γ, s ⊢ t1 <: t2
        // -----------------------
        // ∀s.t1 <: ∀s.t2
        val sFresh = fresh(prefix = "s")
        val t1Inst = t1.subst(s1, Stage.SVar(sFresh))
        val t2Inst = t2.subst(s2, Stage.SVar(sFresh))
        t1Inst.subtype(t2Inst, stenv.addSVar(sFresh))
      case (a, b) =>
        // TODO: Make where this case (reflexivity) is applied more explicit
        if a == b then stenv
        else throw new SubtypeError(s"$t1 </: $t2")

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

    def join(t2: Type, stenv: StEnv): (Type, StEnv) =
      import Subtyping.*

      Try {
        val st1 = t1.subtype(t2, stenv)
        (t2, st1)
      }.orElse(Try {
        val st1 = t2.subtype(t1, stenv)
        (t1, st1)
      }).getOrElse {
        throw new Exception(
          s"Cannot compute join of $t1 and $t2, since neither $t1 <: $t2 nor $t2 <: $t1."
        )
      }

  extension (expr: core.Expr)
    def coerceTo(from: Type, to: Type, stenv: StEnv): core.Expr =
      import core.Expr
      (from, to) match
        case (
              Type.TFun(arg1, ret1),
              Type.TCode(Type.TFun(arg2, ret2))
            ) =>
          // To coerce f: arg1 -> ret1  to  Code[arg2 -> ret2]
          // we create a new function λ x: Code[arg2]. (f (x : arg1) : Code[ret2]), then feed the function to lift
          // TODO: Don't do η-expansion if not necessary
          val newArgName = fresh()
          val newArg = Expr.EVar(newArgName)
          val newArgCoerced = newArg.coerceTo(
            Type.TCode(arg2),
            arg1,
            stenv
          )
          val body = Expr.EApp(
            expr,
            newArgCoerced,
            core.Sta
          )
          val bodyCoerced = body.coerceTo(
            ret1,
            Type.TCode(ret2),
            stenv
          )
          Expr
            .ELift(
              Expr.ELam(
                newArgName,
                Some(Type.TCode(arg2)),
                bodyCoerced,
                Some(Type.TCode(ret2))
              ),
              core.Dyn
            )
            .withType(Type.TCode(Type.TFun(arg2, ret2)))
        case (Type.TFun(arg1, ret1), Type.TFun(arg2, ret2)) =>
          // contravariant in argument, covariant in return
          val newArgName = fresh()
          val newArg = Expr.EVar(newArgName)
          val newArgCoerced = newArg.coerceTo(
            arg2,
            arg1,
            stenv
          )
          val body = Expr.EApp(
            expr,
            newArgCoerced,
            core.Sta
          )
          val bodyCoerced = body.coerceTo(
            ret1,
            ret2,
            stenv
          )
          Expr
            .ELam(
              newArgName,
              Some(arg2),
              bodyCoerced,
              Some(ret2)
            )
            .withType(Type.TFun(arg2, ret2))
        case (Type.TCode(t1), Type.TCode(t2)) => // Code[t1] <: Code[t2]
          // In our current subtyping relation, two types are related only if their erased types are equal. So this case is covered by the reflexivity case below.
          // But if we want to extend the type system with more types, this case should be revisited.
          assert(t1 == t2)
          expr
        case (Type.TBool, Type.TCode(Type.TBool)) |
            (Type.TUnit, Type.TCode(Type.TUnit)) |
            (Type.TInt, Type.TCode(Type.TInt)) =>
          // bool <: Code[bool]
          // unit <: Code[unit]
          // int  <: Code[int]
          Expr.ELift(expr, core.Dyn).withType(to)
        case (Type.TBool | Type.TUnit | Type.TInt, Type.TAt(t, Stage.SVar(s)))
            if t == from =>
          //     s ∈ Γ
          // ---------------
          // int <: int@s

          //     s ∈ Γ
          // ---------------
          // bool <: bool@s

          //     s ∈ Γ
          // ---------------
          // unit <: unit@s
          assert(stenv.containsSVar(s))
          Expr.ELift(expr, Stage.SVar(s)).withType(to)
        case (
              Type.TFun(arg1, ret1),
              Type.TAt(Type.TFun(arg2, ret2), Stage.SVar(s))
            ) =>
          // s ∈ Γ    arg2@s <: arg1   ret1 <: ret2@s
          // ----------------------------------------
          //     arg1 -> ret1 <: (arg2 -> ret2)@s
          assert(stenv.containsSVar(s))
          val newArgName = fresh()
          val newArg = Expr.EVar(newArgName)
          val newArgCoerced = newArg.coerceTo(
            Type.TAt(arg2, Stage.SVar(s)),
            arg1,
            stenv
          )
          val body = Expr.EApp(
            expr,
            newArgCoerced,
            core.Sta
          )
          val bodyCoerced = body.coerceTo(
            ret1,
            Type.TAt(ret2, Stage.SVar(s)),
            stenv
          )
          Expr
            .ELift(
              Expr.ELam(
                newArgName,
                Some(Type.TAt(arg2, Stage.SVar(s))),
                bodyCoerced,
                Some(Type.TAt(ret2, Stage.SVar(s)))
              ),
              Stage.SVar(s)
            )
        case (Type.TForallSt(s1, t1), Type.TForallSt(s2, t2)) =>
          // Γ, s ⊢ t1 <: t2
          // -----------------------
          // ∀s.t1 <: ∀s.t2
          val sFresh = fresh(prefix = "s")
          val t1Inst = t1.subst(s1, Stage.SVar(sFresh))
          val t2Inst = t2.subst(s2, Stage.SVar(sFresh))
          val bodyCoerced = Expr
            .ESApp(expr, Stage.SVar(sFresh))
            .coerceTo(
              t1Inst,
              t2Inst,
              stenv.addSVar(sFresh)
            )
          Expr.ESLam(sFresh, bodyCoerced).withType(to)
        case (a, b) if a == b => expr
        case (a, b) =>
          Try(from.subtype(to, stenv)) match
            case Success(_) =>
              throw new Exception(
                s"Subtyping rules must be problematic, since we don't know how to coerce between $a and $b."
              )

            case Failure(_) =>
              throw new Exception(
                s"Cannot coerce from $a to $b, because $a </: $b."
              )

extension (t: Type)
  def erase: Type = t match
    case Type.TUnit | Type.TInt | Type.TBool => t
    case Type.TFun(arg, ret) =>
      Type.TFun(arg.erase, ret.erase)
    case Type.TForallSt(_, ty) =>
      ty.erase
    case Type.TAt(ty, _) =>
      ty.erase
    case Type.TCode(ty) =>
      Type.TCode(ty.erase)

def inferCall(
    env: Env,
    stenv: StEnv,
    op: core.Expr,
    arg: Expr
): (core.Expr, StEnv) =
  import Subtyping.*
  op.ty.get match
    case Type.TFun(argTy, retTy) =>
      val (e2Typed, stenv2) = check(env, stenv, arg, argTy)
      (core.Expr.EApp(op, e2Typed, core.Sta).withType(retTy), stenv2)
    case Type.TCode(Type.TFun(argTy, retTy)) =>
      val (e2Typed, stenv2) = check(env, stenv, arg, Type.TCode(argTy))
      (
        core.Expr
          .EApp(op, e2Typed, core.Dyn)
          .withType(Type.TCode(retTy)),
        stenv2
      )
    case Type.TAt(Type.TFun(argTy, retTy), s) =>
      val (e2Typed, stenv2) = check(env, stenv, arg, Type.TAt(argTy, s))
      (
        core.Expr.EApp(op, e2Typed, s).withType(Type.TAt(retTy, s)),
        stenv2
      )
    case Type.TForallSt(s, ty) =>
      val existSVar = fresh(prefix = "α")
      val stenv1 = stenv.addExistSVar(existSVar)
      val tyInst = ty.subst(s, Stage.SVar(existSVar))
      val opInst = core.Expr.ESApp(op, Stage.SVar(existSVar)).withType(tyInst)
      inferCall(env, stenv1, opInst, arg)

def infer(env: Env, stenv: StEnv, expr: Expr): (core.Expr, StEnv) =
  import Subtyping.*
  expr match
    case Expr.EUnit =>
      (core.Expr.EUnit.withType(Type.TUnit), stenv)
    case Expr.ENatV(n) =>
      (core.Expr.ENum(n).withType(Type.TInt), stenv)
    case Expr.EVar(x) =>
      (core.Expr.EVar(x).withType(env(x)), stenv)
    case Expr.ELam(x, ty, body) =>
      // Γ, x: argTy ⊢ body ⇐ retTy
      // -------------------------------------------
      // Γ ⊢ λx: argTy. body: retTy ⇒ argTy → retTy
      val (bodyTyped, stenv1) = infer(env + (x -> ty), stenv, body)
      (
        core.Expr
          .ELam(x, Some(ty), bodyTyped, bodyTyped.ty)
          .withType(
            Type.TFun(ty, bodyTyped.ty.get)
          ),
        stenv1
      )
    case Expr.ESLam(s, body) =>
      // Γ, s ⊢ body ⇒ ty
      // ---------------------------
      // Γ ⊢ Λs. body ⇒ ∀s. ty
      val (bodyTyped, stenv1) = infer(env, stenv.addSVar(s), body)
      val sIndex = stenv1.lastIndexOf(StEnvElem.SVar(s))
      (
        core.Expr
          .ESLam(s, bodyTyped)
          .withType(
            Type.TForallSt(s, bodyTyped.ty.get)
          ),
        stenv1.drop(sIndex)
      )
    case Expr.ELet(x, rhs, body) =>
      val (rhsTyped, stenv1) = infer(env, stenv, rhs)
      val (bodyTyped, stenv2) =
        infer(env + (x -> rhsTyped.ty.get), stenv1, body)
      (
        core.Expr.ELet(x, rhsTyped, bodyTyped).withType(bodyTyped.ty.get),
        stenv2
      )
    case Expr.ELift(e, stage) =>
      val (eTyped, stenv1) = infer(env, stenv, e)
      eTyped.ty.get match
        case Type.TInt | Type.TBool | Type.TUnit if stage == core.Dyn =>
          (
            core.Expr
              .ELift(eTyped, core.Dyn)
              .withType(
                Type.TCode(eTyped.ty.get)
              ),
            stenv1
          )
        case Type.TInt | Type.TBool | Type.TUnit
            if stage.isInstanceOf[Stage.SVar] =>
          (
            core.Expr
              .ELift(eTyped, stage)
              .withType(
                Type.TAt(eTyped.ty.get, stage)
              ),
            stenv1
          )
        case Type.TFun(Type.TCode(argTy), Type.TCode(retTy))
            if stage == core.Dyn =>
          (
            core.Expr
              .ELift(eTyped, core.Dyn)
              .withType(
                Type.TCode(Type.TFun(argTy, retTy))
              ),
            stenv1
          )
        case Type.TFun(Type.TAt(argTy, s), Type.TAt(retTy, s1))
            if s == s1 && s == s1 =>
          (
            core.Expr
              .ELift(eTyped, stage)
              .withType(
                Type.TAt(Type.TFun(argTy, retTy), stage)
              ),
            stenv1
          )
    case Expr.ERun(e) =>
      val (eTyped, stenv1) = infer(env, stenv, e)
      (core.Expr.ERun(eTyped).withType(eTyped.ty.get), stenv1)
    case Expr.EApp(e1, e2) =>
      val (e1Typed, stenv1) = infer(env, stenv, e1)
      inferCall(env, stenv1, e1Typed, e2)
    case Expr.ESApp(e, s) =>
      // Γ ⊢ e ⇒ ∀s1. ty
      // --------------------
      // Γ ⊢ e [s] ⇒ ty[s/s1]
      val (eTyped, stenv1) = infer(env, stenv, e)
      val Type.TForallSt(s1, ty) = eTyped.ty.get
      val inst = ty.subst(s1, s)
      (core.Expr.ESApp(eTyped, s).withType(inst), stenv1)
    case Expr.EFix(f, ty, e) =>
      // Γ, f: ty ⊢ e ⇐ ty
      // -------------------------------------------
      // Γ ⊢ fix f: ty. e ⇒ ty
      val (bodyTyped, stenv1) = check(env + (f -> ty), stenv, e, ty)
      val stage = ty match
        case Type.TCode(_)          => core.Dyn
        case Type.TAt(Type.TInt, s) => s
        case _                      => core.Sta
      (core.Expr.EFix(f, bodyTyped, stage).withType(ty), stenv1)
    case Expr.EIfz(cond, thn, els) =>
      val (condTyped, stenv1) = infer(env, stenv, cond)
      condTyped.ty.get match
        case Type.TInt =>
          // Γ ⊢ cond ⇒ Int
          // Γ ⊢ thn ⇒ ty1
          // Γ ⊢ els ⇒ ty2
          // ty1 ⊔ ty2 = ty
          // -----------------------------------
          // Γ ⊢ ifz cond then thn else els ⇒ ty
          val (thnTyped, stenv2) = infer(env, stenv1, thn)
          thnTyped.ty.get match
            case Type.TCode(_) | Type.TAt(_, _) =>
              val (elsTyped, stenv3) = check(env, stenv2, els, thnTyped.ty.get)
              (
                core.Expr
                  .ECond(
                    core.Expr
                      .EBinOp("==", condTyped, core.Expr.ENum(0), core.Sta),
                    thnTyped,
                    elsTyped,
                    core.Sta
                  )
                  .withType(thnTyped.ty.get),
                stenv3
              )
            case _ =>
              val (elsTyped, stenv3) = infer(env, stenv2, els)
              val stenv4 = thnTyped.ty.get.subtype(elsTyped.ty.get, stenv3)
              (
                core.Expr
                  .ECond(
                    core.Expr
                      .EBinOp("==", condTyped, core.Expr.ENum(0), core.Sta),
                    thnTyped,
                    elsTyped,
                    core.Sta
                  )
                  .withType(elsTyped.ty.get),
                stenv4
              )
        case Type.TCode(Type.TInt) =>
          // Γ ⊢ cond ⇒ Code[Int]
          // Γ ⊢ thn ⇒ ty1
          // Γ ⊢ els ⇒ ty2
          // ty1 ⊔ ty2 = Code[_]
          // ------------------------------------------
          // Γ ⊢ ifz cond then thn else els ⇒ ty1 ⊔ ty2
          val (thnTyped, stenv1) = infer(env, stenv, thn)
          thnTyped.ty.get match
            case Type.TCode(_) =>
              val (elsTyped, stenv2) = check(env, stenv1, els, thnTyped.ty.get)
              (
                core.Expr
                  .ECond(
                    core.Expr
                      .EBinOp("==", condTyped, core.Expr.ENum(0), core.Dyn),
                    thnTyped,
                    elsTyped,
                    core.Dyn
                  )
                  .withType(thnTyped.ty.get),
                stenv2
              )
        case Type.TAt(Type.TInt, s) =>
          // Γ ⊢ cond ⇒ Int@s
          // Γ ⊢ thn ⇒ ty1
          // Γ ⊢ els ⇒ ty2
          // ty1 ⊔ ty2 = _@s
          // -----------------------------------
          // Γ ⊢ ifz cond then thn else els ⇒ ty1 ⊔ ty2
          val (thnTyped, stenv1) = infer(env, stenv, thn)
          thnTyped.ty.get match
            case Type.TAt(_, _) =>
              val (elsTyped, stenv2) = check(env, stenv1, els, thnTyped.ty.get)
              (
                core.Expr
                  .ECond(
                    core.Expr.EBinOp("==", condTyped, core.Expr.ENum(0), s),
                    thnTyped,
                    elsTyped,
                    s
                  )
                  .withType(thnTyped.ty.get),
                stenv2
              )
    case Expr.EIf(cond, thn, els) =>
      val (condTyped, stenv1) = infer(env, stenv, cond)
      condTyped.ty.get match
        case Type.TBool =>
          // Γ ⊢ cond ⇒ Bool
          // Γ ⊢ thn ⇒ ty1
          // Γ ⊢ els ⇒ ty2
          // ty1 ⊔ ty2 = ty
          // -----------------------------------
          // Γ ⊢ if cond then thn else els ⇒ ty
          val (thnTyped, stenv2) = infer(env, stenv1, thn)
          thnTyped.ty.get match
            case Type.TCode(_) | Type.TAt(_, _) =>
              val (elsTyped, stenv3) = check(env, stenv2, els, thnTyped.ty.get)
              val stenv4 = thnTyped.ty.get.subtype(elsTyped.ty.get, stenv3)
              (
                core.Expr
                  .ECond(condTyped, thnTyped, elsTyped, core.Sta)
                  .withType(elsTyped.ty.get),
                stenv4
              )
            case _ =>
              val (elsTyped, stenv3) = infer(env, stenv2, els)
              val stenv4 = thnTyped.ty.get.subtype(elsTyped.ty.get, stenv3)
              (
                core.Expr
                  .ECond(condTyped, thnTyped, elsTyped, core.Sta)
                  .withType(elsTyped.ty.get),
                stenv4
              )
        case Type.TCode(Type.TBool) =>
          // Γ ⊢ cond ⇒ Code[Bool]
          // Γ ⊢ thn ⇒ ty1
          // Γ ⊢ els ⇒ ty2
          // ty1 ⊔ ty2 = Code[_]
          // ------------------------------------------
          // Γ ⊢ if cond then thn else els ⇒ ty1 ⊔ ty2
          val (thnTyped, stenv2) = infer(env, stenv1, thn)
          thnTyped.ty.get match
            case Type.TCode(_) =>
              val (elsTyped, stenv3) = check(env, stenv2, els, thnTyped.ty.get)
              val stenv4 = thnTyped.ty.get.subtype(elsTyped.ty.get, stenv3)
              (
                core.Expr
                  .ECond(condTyped, thnTyped, elsTyped, core.Dyn)
                  .withType(thnTyped.ty.get),
                stenv4
              )
        case Type.TAt(Type.TBool, s) =>
          // Γ ⊢ cond ⇒ Bool@s
          // Γ ⊢ thn ⇒ ty1
          // Γ ⊢ els ⇒ ty2
          // ty1 ⊔ ty2 = _@s
          // -----------------------------------
          // Γ ⊢ if cond then thn else els ⇒ ty1 ⊔ ty2
          val (thnTyped, stenv2) = infer(env, stenv1, thn)
          thnTyped.ty.get match
            case Type.TAt(_, _) =>
              val (elsTyped, stenv3) = check(env, stenv2, els, thnTyped.ty.get)
              (
                core.Expr
                  .ECond(condTyped, thnTyped, elsTyped, s)
                  .withType(thnTyped.ty.get),
                stenv3
              )
    case Expr.EBin(op, left, right) =>
      op match
        case "+" | "-" | "*" | "/" =>
          // Γ ⊢ e1 ⇒ ty1
          // Γ ⊢ e2 ⇒ ty2
          // |ty1 ⊔ ty2| <: Int
          // -------------------------------------------
          // Γ ⊢ e1 + e2 ⇒ ty1 ⊔ ty2
          val (leftTyped, stenv1) = infer(env, stenv, left)
          leftTyped.ty.get match
            case Type.TCode(_) | Type.TAt(_, _) =>
              val (rightTyped, stenv2) =
                check(env, stenv1, right, leftTyped.ty.get)
              (
                core.Expr
                  .EBinOp(op, leftTyped, rightTyped, core.Dyn)
                  .withType(leftTyped.ty.get),
                stenv2
              )
            case _ =>
              val (rightTyped, stenv2) = infer(env, stenv1, right)
              val stenv3 = leftTyped.ty.get.erase.subtype(Type.TInt, stenv2)
              val stage = rightTyped.ty.get match
                case Type.TCode(_)          => core.Dyn
                case Type.TAt(Type.TInt, s) => s
                case _                      => core.Sta
              (
                core.Expr
                  .EBinOp(op, leftTyped, rightTyped, stage)
                  .withType(leftTyped.ty.get),
                stenv3
              )
        case "==" | "!=" | "<" | "<=" | ">" | ">=" =>
          // Γ ⊢ e1 ⇒ ty1
          // Γ ⊢ e2 ⇒ ty2
          // |ty1 ⊔ ty2| <: Int
          // ---------------------------------------------------------------------------------------
          // Γ ⊢ e1 == e2 ⇒ f(ty1 ⊔ ty2) where f(Code[t]) = Code[Bool], f(t@s) = Bool@s, f(t) = Bool
          def f(t: Type): Type = t match
            case Type.TCode(_)  => Type.TCode(Type.TBool)
            case Type.TAt(_, s) => Type.TAt(Type.TBool, s)
            case _              => Type.TBool

          val (leftTyped, stenv1) = infer(env, stenv, left)
          leftTyped.ty.get match
            case Type.TCode(Type.TInt) | Type.TAt(Type.TInt, _) =>
              val (rightTyped, stenv2) =
                check(env, stenv1, right, leftTyped.ty.get)
              val retType = f(leftTyped.ty.get)
              (
                core.Expr
                  .EBinOp(op, leftTyped, rightTyped, core.Dyn)
                  .withType(retType),
                stenv2
              )
            case _ =>
              val (rightTyped, stenv2) = infer(env, stenv1, right)
              val stage = rightTyped.ty.get match
                case Type.TCode(_)          => core.Dyn
                case Type.TAt(Type.TInt, s) => s
                case _                      => core.Sta
              (
                core.Expr
                  .EBinOp(op, leftTyped, rightTyped, stage)
                  .withType(rightTyped.ty.get),
                stenv2
              )
    case Expr.EAlloc(e)       => ???
    case Expr.EGet(e)         => ???
    case Expr.EPut(e1, e2)    => ???
    case Expr.EAscribe(e, ty) =>
      // Γ ⊢ e ⇐ ty
      // -----------------
      // Γ ⊢ (e : ty) ⇒ ty
      val (eTyped, stenv1) = infer(env, stenv, e)
      val stenv2 = eTyped.ty.get.subtype(ty, stenv1)
      (eTyped.withType(ty), stenv2)

def check(
    env: Env,
    stenv: StEnv,
    expr: Expr,
    expected: Type
): (core.Expr, StEnv) =
  import Subtyping.*
  // Γ ⊢ expr ⇒ ty
  // ty <: expected
  // -----------------------
  // Γ ⊢ expr ⇐ expected
  val (exprTyped, stenv1) = infer(env, stenv, expr)
  val stenv2 = exprTyped.ty.get.subtype(expected, stenv1)
  (exprTyped, stenv2)
