package instar.experiment.tyck

import instar.experiment.eff as core
import instar.experiment.eff.Type
import instar.experiment.eff.Stage

import instar.experiment.surf.*
import instar.Counter.fresh
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

  def lookupUnboundSVar(svar: Stage): Int =
    svar match
      case Stage.ExistSVar(x) =>
        stenv.lastIndexOf(StEnvElem.ExistSVar(x))
      case Stage.SVar(x) =>
        stenv.lastIndexOf(StEnvElem.SVar(x))

  def lookupBoundSVar(svar: Stage.ExistSVar): Option[Stage] =
    stenv.reverseIterator.collectFirst {
      case StEnvElem.ExistSVarBound(x, bound) if x == svar.x => bound
    }

  def apply(t: Type): Type = t match
    case Type.TUnit | Type.TInt | Type.TBool => t
    case Type.TFun(arg, ret) =>
      Type.TFun(stenv(arg), stenv(ret))
    case Type.TForallSt(s, ty) =>
      Type.TForallSt(s, stenv(ty))
    case Type.TAt(ty, st) =>
      Type.TAt(stenv(ty), stenv(st))
    case Type.TCode(ty) =>
      Type.TCode(stenv(ty))

  def apply(s: Stage): Stage = s match
    case Stage.SNum(n) => Stage.SNum(n)
    case Stage.SVar(v) => Stage.SVar(v)
    case sv @ Stage.ExistSVar(x) =>
      stenv.lookupBoundSVar(sv) match
        case Some(bound) => bound
        case None        => sv

  def apply(e: core.Expr): core.Expr = e match
    case core.Expr.EUnit =>
      e
    case core.Expr.ENum(_) =>
      e
    case core.Expr.EVar(_) =>
      e.withType(stenv(e.ty.get))
    case core.Expr.ELam(x, tyOpt, body, retTyOpt) =>
      val tyOpt1 = tyOpt.map(stenv(_))
      val body1 = stenv(body)
      val retTyOpt1 = retTyOpt.map(stenv(_))
      core.Expr
        .ELam(x, tyOpt1, body1, retTyOpt1)
        .withType(
          stenv(e.ty.get)
        )
    case core.Expr.ESLam(s, body) =>
      val body1 = stenv(body)
      core.Expr
        .ESLam(s, body1)
        .withType(
          stenv(e.ty.get)
        )
    case core.Expr.ELet(x, rhs, body) =>
      val rhs1 = stenv(rhs)
      val body1 = stenv(body)
      core.Expr.ELet(x, rhs1, body1).withType(stenv(e.ty.get))
    case core.Expr.ELift(e, stage) =>
      val e1 = stenv(e)
      val stage1 = stenv(stage)
      core.Expr
        .ELift(e1, stage1)
        .withType(
          stenv(e.ty.get)
        )
    case core.Expr.ERun(e) =>
      val e1 = stenv(e)
      core.Expr.ERun(e1).withType(stenv(e.ty.get))
    case core.Expr.EApp(e1, e2, stage) =>
      val e1Typed = stenv(e1)
      val e2Typed = stenv(e2)
      val stage1 = stenv(stage)
      core.Expr
        .EApp(e1Typed, e2Typed, stage1)
        .withType(
          stenv(e.ty.get)
        )
    case core.Expr.ESApp(e, s) =>
      val e1 = stenv(e)
      val s1 = stenv(s)
      core.Expr
        .ESApp(e1, s1)
        .withType(
          stenv(e.ty.get)
        )
    case core.Expr.EFix(f, body, stage) =>
      val body1 = stenv(body)
      val stage1 = stenv(stage)
      core.Expr
        .EFix(f, body1, stage1)
        .withType(
          stenv(e.ty.get)
        )
    case core.Expr.ECond(cond, thn, els, stage) =>
      val cond1 = stenv(cond)
      val thn1 = stenv(thn)
      val els1 = stenv(els)
      val stage1 = stenv(stage)
      core.Expr
        .ECond(cond1, thn1, els1, stage1)
        .withType(
          stenv(e.ty.get)
        )
    case core.Expr.EBinOp(op, left, right, stage) =>
      val left1 = stenv(left)
      val right1 = stenv(right)
      val stage1 = stenv(stage)
      core.Expr
        .EBinOp(op, left1, right1, stage1)
        .withType(
          stenv(e.ty.get)
        )
    case core.Expr.EUnaryOp(op, expr, stage) =>
      val expr1 = stenv(expr)
      val stage1 = stenv(stage)
      core.Expr
        .EUnaryOp(op, expr1, stage1)
        .withType(
          stenv(e.ty.get)
        )
    case core.Expr.EAscribe(expr, ty) =>
      val expr1 = stenv(expr)
      val ty1 = stenv(ty)
      core.Expr
        .EAscribe(expr1, ty1)
        .withType(
          stenv(e.ty.get)
        )

object Subtyping:

  case class SubtypeError(message: String) extends Exception(message)

  extension (svar: Stage.ExistSVar)
    // instantiate s1 to s2
    def inst(s2: Stage, stenv: StEnv): StEnv =
      val index = stenv.lookupUnboundSVar(svar)
      stenv.updated(
        index,
        StEnvElem.ExistSVarBound(svar.x, s2)
      )

  extension (s1: Stage)
    def subtype(s2: Stage, stenv: StEnv): StEnv = (s1, s2) match
      case (Stage.SNum(n1), Stage.SNum(n2)) if n1 <= n2 =>
        stenv
      case (Stage.SVar(v1), Stage.SVar(v2)) if v1 == v2 =>
        stenv
      case (Stage.SNum(0), Stage.SVar(v2)) =>
        stenv
      case (Stage.SVar(v1), sv @ Stage.ExistSVar(_)) =>
        sv.inst(s1, stenv)
      case (Stage.SNum(_), sv @ Stage.ExistSVar(_)) =>
        sv.inst(s1, stenv)
      case (sv @ Stage.ExistSVar(_), Stage.SVar(v2)) =>
        sv.inst(s2, stenv)
      case (sv @ Stage.ExistSVar(_), Stage.SNum(_)) =>
        sv.inst(s2, stenv)
      case (sv1 @ Stage.ExistSVar(_), sv2 @ Stage.ExistSVar(_)) =>
        // sv1 <: sv2
        // update the newer bound to be the older bound
        val sv1Index = stenv.lookupUnboundSVar(sv1)
        val sv2Index = stenv.lookupUnboundSVar(sv2)
        if sv1Index > sv2Index then
          stenv.updated(
            sv1Index,
            StEnvElem.ExistSVarBound(sv1.x, sv2)
          )
        else
          stenv.updated(
            sv2Index,
            StEnvElem.ExistSVarBound(sv2.x, sv1)
          )

  extension (t1: Type)
    def detach: (Type, Stage) = t1 match
      case Type.TAt(t, s) => (t, s)
      case Type.TCode(t)  => (t, Stage.SNum(1))
      case _              => (t1, Stage.SNum(0))

    def push0(s: Stage): Type =
      def push1(t1: Type, s: Stage): Type =
        s match
          case Stage.SNum(0) => t1
          case (Stage.SVar(_) | Stage.SNum(1)) =>
            t1 match
              case Type.TInt | Type.TAt(Type.TInt, Stage.SNum(0)) =>
                Type.TAt(Type.TInt, s)
              case Type.TBool | Type.TAt(Type.TBool, Stage.SNum(0)) =>
                Type.TAt(Type.TBool, s)
              case Type.TUnit | Type.TAt(Type.TUnit, Stage.SNum(0)) |
                  Type.TCode(Type.TUnit) =>
                Type.TAt(Type.TUnit, s)
              case Type.TFun(arg, ret) => Type.TAt(t1, s)
              case Type.TAt(Type.TFun(arg, ret), Stage.SNum(0)) =>
                Type.TAt(t1, s)
          case Stage.ExistSVar(x) => ???

      t1 match
        case Type.TInt  => Type.TInt
        case Type.TBool => Type.TBool
        case Type.TUnit => Type.TUnit
        case Type.TFun(arg, ret) =>
          Type.TFun(push1(arg, s), push1(ret, s))

    // Subtyping relation: t1 <: t2
    def subtype(t2: Type, stenv: StEnv): StEnv =
      (t1, t2) match
        case (Type.TForallSt(s1, t1), Type.TForallSt(s2, t2)) =>
          // Γ, s ⊢ t1 <: t2
          // -----------------------
          // ∀s.t1 <: ∀s.t2
          val sFresh = fresh(prefix = "s")
          val t1Inst = t1.subst(s1, Stage.SVar(sFresh))
          val t2Inst = t2.subst(s2, Stage.SVar(sFresh))
          val stenv1 = t1Inst.subtype(t2Inst, stenv.addSVar(sFresh))
          stenv1.drop(stenv1.indexOf(StEnvElem.SVar(sFresh)) + 1)
        case (Type.TFun(arg1, ret1), Type.TFun(arg2, ret2)) =>
          // contravariant in argument, covariant in return
          val stenv1 = arg2.subtype(arg1, stenv)
          ret1.subtype(ret2, stenv1)
        case (Type.TUnit, Type.TUnit) | (Type.TInt, Type.TInt) |
            (Type.TBool, Type.TBool) =>
          stenv
        case _ =>
          val (base1, stage1) = t1.detach
          val (base2, stage2) = t2.detach
          val stenv1 = stage1.subtype(stage2, stenv)
          base1
            .push0(stage1)
            .subtype(
              base2.push0(stage2),
              stenv1
            )

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
          // nat  <: Code[nat]
          Expr.ELift(expr, core.Dyn).withType(to)
        case (Type.TBool | Type.TUnit | Type.TInt, Type.TAt(t, Stage.SVar(s)))
            if t == from =>
          assert(stenv.containsSVar(s))
          Expr.ELift(expr, Stage.SVar(s)).withType(to)
        case (
              Type.TFun(arg1, ret1),
              Type.TAt(Type.TFun(arg2, ret2), Stage.SVar(s))
            ) =>
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
      val tyInst = ty.subst(s, Stage.ExistSVar(existSVar))
      val opInst =
        core.Expr.ESApp(op, Stage.ExistSVar(existSVar)).withType(tyInst)
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
      val sIndex = stenv1.lookupUnboundSVar(Stage.SVar(s))
      (
        core.Expr
          .ESLam(s, bodyTyped)
          .withType(
            Type.TForallSt(s, bodyTyped.ty.get)
          ),
        stenv1.drop(sIndex + 1)
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
      inferCall(env, stenv1, stenv1(e1Typed), e2)
    case Expr.ESApp(e, s) =>
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
      val condTypedApplied = stenv1(condTyped.ty.get)
      condTypedApplied match
        case Type.TInt | Type.TAt(Type.TInt, Stage.SNum(0)) =>
          val (thnTyped, stenv2) = infer(env, stenv1, thn)
          val thnTypedApplied = stenv2(thnTyped.ty.get)
          thnTypedApplied match
            case Type.TCode(_) | Type.TAt(_, Stage.SVar(_)) |
                Type.TAt(_, Stage.SNum(1)) | Type.TAt(_, Stage.ExistSVar(_)) =>
              // Γ |- e1 => nat^1
              // Γ |- e2 => t2^s (s could be an existential stage variable)
              // Γ |- e3 <= t2^s
              // -----------------------------------
              // Γ |- ifz e1 then e2 else e3 ⇒ t2^s
              val (elsTyped, stenv3) =
                check(env, stenv2, els, thnTypedApplied)
              (
                core.Expr
                  .ECond(
                    core.Expr
                      .EBinOp("==", condTyped, core.Expr.ENum(0), core.Sta),
                    thnTyped,
                    elsTyped,
                    core.Sta
                  )
                  .withType(thnTypedApplied),
                stenv3
              )
            case _ =>
              // Γ |- e1 => nat^1
              // Γ |- e2 => t2^1
              // Γ |- e3 => t2^s
              // -----------------------------------
              // Γ |- ifz e1 then e2 else e3 ⇒ t2^s
              val (elsTyped, stenv3) = infer(env, stenv2, els)
              val elsTypedApplied = stenv3(elsTyped.ty.get)
              val stenv4 = thnTypedApplied.subtype(elsTypedApplied, stenv3)
              (
                core.Expr
                  .ECond(
                    core.Expr
                      .EBinOp("==", condTyped, core.Expr.ENum(0), core.Sta),
                    thnTyped,
                    elsTyped,
                    core.Sta
                  )
                  .withType(elsTypedApplied),
                stenv4
              )
        case Type.TCode(Type.TInt) | Type.TAt(Type.TInt, Stage.SVar(_)) |
            Type.TAt(Type.TInt, Stage.SNum(1)) | Type.TAt(Type.TInt, Stage.ExistSVar(_)) =>
          // Γ |- e1 => nat^s
          // Γ |- e2 => t2^s
          // Γ |- e3 <= t2^s
          // -----------------------------------
          // Γ |- ifz e1 then e2 else e3 ⇒ t2^s
          val (thnTyped, stenv2) = infer(env, stenv, thn)
          val thnTypedApplied = stenv2(thnTyped.ty.get)
          thnTypedApplied match
            case Type.TCode(_) | Type.TAt(_, Stage.SVar(_)) |
                Type.TAt(_, Stage.SNum(1)) =>
              val (elsTyped, stenv3) = check(env, stenv2, els, thnTypedApplied)
              (
                core.Expr
                  .ECond(
                    core.Expr
                      .EBinOp("==", condTyped, core.Expr.ENum(0), core.Dyn),
                    thnTyped,
                    elsTyped,
                    core.Dyn
                  )
                  .withType(thnTypedApplied),
                stenv3
              )
        case Type.TAt(Type.TInt, s) => ???

    case Expr.EIf(cond, thn, els) =>
      val (condTyped, stenv1) = infer(env, stenv, cond)
      val condTypedApplied = stenv1(condTyped.ty.get)
      condTypedApplied match
        case (Type.TBool | Type.TAt(Type.TBool, Stage.SNum(0))) =>
          val (thnTyped, stenv2) = infer(env, stenv1, thn)
          val thnTypedApplied = stenv2(thnTyped.ty.get)
          thnTypedApplied match
            case Type.TCode(_) | Type.TAt(_, Stage.SNum(1)) |
                Type.TAt(_, Stage.SVar(_)) | Type.TAt(_, Stage.ExistSVar(_)) =>
              // Γ |- e1 => bool
              // Γ |- e2 => t2^s
              // Γ |- e3 <= t2^s
              // -----------------------------------
              // Γ |- if e1 then e2 else e3 ⇒ t2^s
              val (elsTyped, stenv3) = check(env, stenv2, els, thnTypedApplied)
              val elsTypedApplied = stenv3(elsTyped.ty.get)
              val stenv4 =
                stenv3(thnTypedApplied).subtype(elsTypedApplied, stenv3)
              (
                core.Expr
                  .ECond(condTyped, thnTyped, elsTyped, core.Sta)
                  .withType(elsTypedApplied),
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
        case Type.TCode(Type.TBool) | Type.TAt(Type.TBool, Stage.SVar(_)) |
            Type.TAt(Type.TBool, Stage.SNum(1)) =>
          // Γ |- e1 => bool^s, s = 2 or s is a non-existential stage variable
          // Γ |- e2 => t2^s
          // Γ |- e3 <= t2^s
          // -----------------------------------
          // Γ |- if e1 then e2 else e3 ⇒ t2^s
          val (thnTyped, stenv2) = infer(env, stenv1, thn)
          val thnTypedApplied = stenv2(thnTyped.ty.get)
          thnTypedApplied match
            case Type.TCode(_) =>
              val (elsTyped, stenv3) = check(env, stenv2, els, thnTypedApplied)
              (
                core.Expr
                  .ECond(condTyped, thnTyped, elsTyped, core.Dyn)
                  .withType(elsTyped.ty.get),
                stenv3
              )
        case Type.TAt(Type.TBool, Stage.ExistSVar(_)) => ???
    case Expr.EBin(op, left, right) =>
      op match
        case "+" | "-" | "*" | "/" =>
          val (leftTyped, stenv1) = infer(env, stenv, left)
          val leftTypedApplied = stenv1(leftTyped.ty.get)
          leftTypedApplied match
            case Type.TCode(Type.TInt) | Type.TAt(Type.TInt, Stage.SNum(1)) |
                Type.TAt(Type.TInt, Stage.SVar(_)) =>
              // Γ |- e1 => nat^s, s = 2 or s is a non-existential stage variable
              // Γ |- e2 <= nat^s
              // -------------------  ----------------
              // Γ |- e1 + e2 ⇒ nat^s
              val (rightTyped, stenv2) =
                check(env, stenv1, right, leftTypedApplied)
              val stage = leftTypedApplied match
                case Type.TCode(_)          => core.Dyn
                case Type.TAt(Type.TInt, s) => s
                case _                      => core.Sta
              (
                core.Expr
                  .EBinOp(op, leftTyped, rightTyped, stage)
                  .withType(rightTyped.ty.get),
                stenv2
              )
            case Type.TInt | Type.TAt(Type.TInt, Stage.SNum(0)) =>
              // Γ |- e1 => nat^1
              // Γ |- e2 => nat^s
              // -----------------------------------
              // Γ |- e1 + e2 ⇒ nat^s
              val (rightTyped, stenv2) = infer(env, stenv1, right)
              val rightTypedApplied = stenv2(rightTyped.ty.get)
              rightTypedApplied match
                case Type.TInt | Type.TCode(Type.TInt) |
                    Type.TAt(Type.TInt, _) =>
                  val stage = rightTypedApplied match
                    case Type.TCode(_)          => core.Dyn
                    case Type.TAt(Type.TInt, s) => s
                    case _                      => core.Sta
                  (
                    core.Expr
                      .EBinOp(op, leftTyped, rightTyped, stage)
                      .withType(leftTyped.ty.get),
                    stenv2
                  )
            case Type.TAt(Type.TInt, Stage.ExistSVar(_)) => ???
        case "==" | "!=" | "<" | "<=" | ">" | ">=" =>
          def f(t: Type): Type = t match
            case Type.TCode(_)  => Type.TCode(Type.TBool)
            case Type.TAt(_, s) => Type.TAt(Type.TBool, s)
            case _              => Type.TBool

          val (leftTyped, stenv1) = infer(env, stenv, left)
          val leftTypedApplied = stenv1(leftTyped.ty.get)
          leftTypedApplied match
            case Type.TCode(Type.TInt) | Type.TAt(Type.TInt, Stage.SVar(_)) |
                Type.TAt(Type.TInt, Stage.SNum(1)) =>
              // Γ |- e1 => nat^s, s = 2 or s is a non-existential stage variable
              // Γ |- e2 <= nat^s
              // -----------------------------------
              // Γ |- e1 op e2 ⇒ bool^s
              val (rightTyped, stenv2) =
                check(env, stenv1, right, leftTypedApplied)
              val stage = rightTyped.ty.get match
                case Type.TCode(_)          => core.Dyn
                case Type.TAt(Type.TInt, s) => s
                case _                      => core.Sta
              (
                core.Expr
                  .EBinOp(op, leftTyped, rightTyped, stage)
                  .withType(f(rightTyped.ty.get)),
                stenv2
              )
            case Type.TInt | Type.TAt(Type.TInt, Stage.SNum(0)) =>
              // Γ |- e1 => nat^1
              // Γ |- e2 => nat^s
              // -----------------------------------
              // Γ |- e1 op e2 ⇒ bool^s
              val (rightTyped, stenv2) = infer(env, stenv1, right)
              val rightTypedApplied = stenv2(rightTyped.ty.get)
              rightTypedApplied match
                case Type.TInt | Type.TCode(Type.TInt) |
                    Type.TAt(Type.TInt, _) =>
                  val stage = rightTypedApplied match
                    case Type.TCode(_)          => core.Dyn
                    case Type.TAt(Type.TInt, s) => s
                    case _                      => core.Sta
                  (
                    core.Expr
                      .EBinOp(op, leftTyped, rightTyped, stage)
                      .withType(f(rightTyped.ty.get)),
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
  (exprTyped.withType(expected), stenv2)
