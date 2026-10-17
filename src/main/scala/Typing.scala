package instar.typing

import instar.syntax.*
import Expr.*
import Stage.*
import StageConstraints.*
import Type.*

object Counter:
  private var count: Int = 0
  def reset(): Unit = count = 0
  def fresh: String =
    val c = count
    count += 1
    s"$$s$c"

final class TypeException(message: String) extends RuntimeException(message)

private case class Ctx(
  env: Map[String, Type] = Map(),
  stEnv: Map[String, Set[StageConstraint]] = Map(),
):
  def +(xt: (String, Type)): Ctx = copy(env = env + xt)
  def +(s: String, cs: List[StageConstraint]): Ctx =
    assert(!containsStVar(s), s"stage variable `$s` is already bound")
    val extended = copy(stEnv = stEnv + (s -> cs.toSet))
    cs.foreach { c => WF.check(extended, c.lower); WF.check(extended, c.upper) }
    extended
  def constraints: List[StageConstraint] = stEnv.valuesIterator.flatten.toSet.toList
  def containsVar(x: String): Boolean = env.contains(x)
  def containsStVar(x: String): Boolean = stEnv.contains(x)
  def apply(x: String): Type = env(x)

private object WF:
  def check(ctx: Ctx, st: Stage): Unit =
    st match
      case SNum(1) | SNum(2) => ()
      case SNum(n) => fail(s"unsupported stage $n; expected 1 or 2")
      case SVar(s) =>
        assert(ctx.containsStVar(s), s"unbound stage variable `$s`")
      case SJoin(a, b) =>
        check(ctx, a)
        check(ctx, b)

  def check(ctx: Ctx, ty: Type): Unit =
    val base = ty.base
    val st = ty.stage
    check(ctx, st)
    base match
      case TInt | TBool | TUnit => ()
      case TFun(arg, ret) =>
        check(ctx, arg)
        check(ctx, ret)
        ctx.constraints.assertStLeq(st, arg.stage)
        ctx.constraints.assertStLeq(st, ret.stage)
      case TRef(inner) =>
        check(ctx, inner)
        ctx.constraints.assertStLeq(st, inner.stage)
      case TForallSt(s, body, constraints) =>
        assert(ctx.constraints.implyStEq(st, Sta), "stage abstractions must be at stage 1")
        if ctx.containsStVar(s) then
          val fresh = Counter.fresh
          check(ctx + (fresh, Subst.constraints(constraints, s, SVar(fresh))),
            Subst.ty(body, s, SVar(fresh)))
        else check(ctx + (s, constraints), body)
      case TAt(_, _) => fail("unexpected outer type annotation")

def infer(expr: Expr): Expr =
  Counter.reset()
  infer(Ctx(), expr)

def check(expr: Expr, expected: Type): Expr =
  Counter.reset()
  val ctx = Ctx()
  WF.check(ctx, expected)
  check(ctx, expr, expected)

private def infer(ctx: Ctx, expr: Expr): Expr =
  expr match
    case EUnit => EUnit.withType(TUnit)
    case ENum(i) => ENum(i).withType(TInt)
    case EBool(b) => EBool(b).withType(TBool)

    case EVar(x) =>
      assert(ctx.containsVar(x), s"unbound variable `$x`")
      EVar(x).withType(ctx(x))

    case ELam(x, Some(argTy), body, Some(retTy)) =>
      WF.check(ctx, argTy)
      WF.check(ctx, retTy)
      val tyBody = check(ctx + (x -> argTy), body, retTy)
      ELam(x, Some(argTy), tyBody, Some(retTy)).withType(TFun(argTy, retTy))

    case ELam(x, Some(argTy), body, None) =>
      WF.check(ctx, argTy)
      val tyBody = infer(ctx + (x -> argTy), body)
      ELam(x, Some(argTy), tyBody, tyBody.ty).withType(TFun(argTy, tyBody.ty.get))

    case ELam(_, None, _, _) =>
      fail("cannot infer a lambda without a parameter type")

    case lam: ESLam if ctx.containsStVar(lam.s) =>
      infer(ctx, freshenStageBinder(lam))
    case ESLam(s, body, constraints) =>
      val typedBody = infer(ctx + (s, constraints), body)
      val bodyTy = typedBody.ty.get
      ESLam(s, typedBody, constraints).withType(TForallSt(s, bodyTy, constraints))

    case ESApp(e, st) =>
      WF.check(ctx, st)
      val typedFun = infer(ctx, e)
      typedFun.ty.get.base match
        case TForallSt(s, bodyTy, constraints) =>
          Subst.constraints(constraints, s, st).foreach { c =>
            ctx.constraints.assertStLeq(c.lower, c.upper)
          }
          ESApp(typedFun, st).withType(Subst.ty(bodyTy, s, st))
        case other => fail(s"expected a stage-polymorphic type, found $other")

    case EApp(e1, e2, None) =>
      val typedFun = infer(ctx, e1)
      val funTy = typedFun.ty.get
      funTy.base match
        case TFun(argTy, resTy) =>
          val typedArg = check(ctx, e2, argTy)
          EApp(typedFun, typedArg, Some(funTy.stage)).withType(resTy)
        case _ => fail(s"expected a function, found $funTy")

    case EApp(e1, e2, Some(st)) =>
      WF.check(ctx, st)
      val typedFun = infer(ctx, e1)
      val funTy = typedFun.ty.get
      funTy.base match
        case TFun(argTy, resTy) =>
          assert(ctx.constraints.implyStEq(funTy.stage, st),
            s"function stage ${funTy.stage} does not match application stage $st")
          val typedArg = check(ctx, e2, argTy)
          EApp(typedFun, typedArg, Some(st)).withType(resTy)
        case _ => fail(s"expected a function, found $funTy")

    case ELift(e, st) =>
      val typed = infer(ctx, e)
      val ty = typed.ty.get
      WF.check(ctx, st)
      ctx.constraints.assertStLeq(ty.stage, st)
      ty.base match
        case TInt | TBool | TUnit => ()
        case TFun(arg, ret) =>
          ctx.constraints.assertStLeq(st, arg.stage)
          ctx.constraints.assertStLeq(st, ret.stage)
        case _ if ctx.constraints.implyStEq(ty.stage, st) => ()
        case _ => fail(s"cannot lift type $ty to $st")
      ELift(typed, st).withType(ty.at(st))

    case ERun(e) =>
      val typedInner = infer(Ctx(), e)
      val innerTy = typedInner.ty.get
      if Nil.implyStEq(innerTy.stage, Dyn) then
        ERun(typedInner).withType(innerTy.erase)
      else fail(s"`run` expects `Code[T]`, found $innerTy")

    case ELet(x, rhs, body) =>
      val typedRhs = infer(ctx, rhs)
      WF.check(ctx, typedRhs.ty.get)
      val typedBody = infer(ctx + (x -> typedRhs.ty.get), body)
      val resultTy = typedBody.ty.get.at(typedRhs.ty.get.stage)
      ELet(x, typedRhs, coerce(ctx, typedBody, resultTy)).withType(resultTy)

    case ELetRec(f, EAscribe(rhs, ty), body, explicitStage) =>
      WF.check(ctx, ty)
      val st = ty.stage
      explicitStage.foreach { s =>
        WF.check(ctx, s)
        assert(ctx.constraints.implyStEq(s, st), s"letrec stage $s does not match recursive type $ty")
      }
      val recursiveCtx = ctx + (f -> ty)
      val typedRhs = check(recursiveCtx, rhs, ty)
      val delayed = ty.base match
        case TFun(arg, ret) =>
          val x = Counter.fresh
          val call = EApp(typedRhs, EVar(x).withType(arg), Some(st)).withType(ret)
          val lam = ELam(x, Some(arg), call, Some(ret)).withType(TFun(arg, ret))
          ELift(lam, st).withType(ty)
        case TForallSt(s, inner, constraints) =>
          val fresh = Counter.fresh
          val stage = SVar(fresh)
          val call = ESApp(typedRhs, stage).withType(Subst.ty(inner, s, stage))
          ESLam(fresh, call, Subst.constraints(constraints, s, stage)).withType(ty)
        case _ => fail(s"letrec requires a function or stage-polymorphic type, found $ty")
      val typedBody = infer(recursiveCtx, body)
      val resultTy = typedBody.ty.get.at(st)
      ELetRec(f, delayed, coerce(recursiveCtx, typedBody, resultTy), Some(st)).withType(resultTy)
    case ELetRec(f, _, _, _) =>
      fail(s"recursive `letrec` binding `$f` needs a type annotation or an annotated function header")

    case ECond(cond, thn, els, stage) =>
      val typedCond = stage match
        case Some(st) =>
          WF.check(ctx, st)
          check(ctx, cond, TBool.at(st))
        case None => infer(ctx, cond)
      val condTy = typedCond.ty.get.base
      val condStage = typedCond.ty.get.stage
      assert(condTy == TBool, s"expected a Boolean condition, found ${typedCond.ty.get}")
      val typedThen = infer(ctx, thn)
      val typedElse = infer(ctx, els)
      val thenTy = typedThen.ty.get
      val elseTy = typedElse.ty.get
      assert(ctx.constraints.implyTyEq(thenTy.at(Sta), elseTy.at(Sta)),
        s"conditional branches have different base types: $thenTy and $elseTy")
      val resultTy = thenTy.at(condStage | thenTy.stage | elseTy.stage)
      ECond(typedCond, coerce(ctx, typedThen, resultTy),
        coerce(ctx, typedElse, resultTy), Some(condStage)).withType(resultTy)

    case EBinOp(op, e1, e2, None) =>
      val typedL = infer(ctx, e1)
      val typedR = infer(ctx, e2)
      val st = typedL.ty.get.stage | typedR.ty.get.stage
      val (argTy, resTy) = inferBinOp(op, st)
      EBinOp(op, coerce(ctx, typedL, argTy),
        coerce(ctx, typedR, argTy), Some(st)).withType(resTy)

    case EBinOp(op, e1, e2, Some(st)) =>
      WF.check(ctx, st)
      val (argTy, resTy) = inferBinOp(op, st)
      val typedL = check(ctx, e1, argTy)
      val typedR = check(ctx, e2, argTy)
      EBinOp(op, typedL, typedR, Some(st)).withType(resTy)

    case EUnaryOp(op, e, None) =>
      val typed = infer(ctx, e)
      val st = typed.ty.get.stage
      val (argTy, resultTy) = inferUnaryOp(op, st)
      EUnaryOp(op, coerce(ctx, typed, argTy), Some(st)).withType(resultTy)

    case EUnaryOp(op, e, Some(st)) =>
      WF.check(ctx, st)
      val (argTy, resTy) = inferUnaryOp(op, st)
      val typedE = check(ctx, e, argTy)
      EUnaryOp(op, typedE, Some(st)).withType(resTy)

    case EAlloc(e, None) => infer(ctx, EAlloc(e, Some(Sta)))

    case EAlloc(e, Some(st)) =>
      WF.check(ctx, st)
      val typedE = infer(ctx, e)
      val elemTy = typedE.ty.get
      ctx.constraints.assertStLeq(st, elemTy.stage)
      EAlloc(typedE, Some(st)).withType(TRef(elemTy).at(st))

    case EDeref(e, None) => infer(ctx, EDeref(e, Some(Sta)))

    case EDeref(e, Some(st)) =>
      WF.check(ctx, st)
      val typedE = infer(ctx, e)
      val refTy = typedE.ty.get
      refTy.base match
        case TRef(elemTy) =>
          assert(ctx.constraints.implyStEq(refTy.stage, st),
            s"reference stage ${refTy.stage} does not match dereference stage $st")
          EDeref(typedE, Some(st)).withType(elemTy)
        case other =>
          fail(s"`!` expects a reference, found $other")

    case EAssign(e1, e2, None) => infer(ctx, EAssign(e1, e2, Some(Sta)))

    case EAssign(e1, e2, Some(st)) =>
      WF.check(ctx, st)
      val typedL = infer(ctx, e1)
      val refTy = typedL.ty.get
      refTy.base match
        case TRef(elemTy) =>
          assert(ctx.constraints.implyStEq(refTy.stage, st),
            s"reference stage ${refTy.stage} does not match assignment stage $st")
          val typedR = check(ctx, e2, elemTy)
          EAssign(typedL, typedR, Some(st)).withType(TUnit.at(st))
        case other =>
          fail(s"`:=` expects a reference on the left, found $other")

    case EAscribe(e, ty) =>
      WF.check(ctx, ty)
      check(ctx, e, ty)

    case ELoc(_) =>
      fail("cannot type-check internal location expressions")

    // Experimental:

    case EIsApp(e) =>
      val typedE = infer(ctx, e)
      typedE.ty.getOrElse(fail("internal error: isApp argument is missing a type")) match
        case ty if ctx.constraints.implyStEq(ty.stage, Dyn) => EIsApp(typedE).withType(TBool)
        case other => fail(s"`isApp` expects `Code[T]`, found $other")

    case ECBNApp(e1, e2) =>
      val typedFun = infer(ctx, e1)
      typedFun.ty.get.base match
        case TFun(argTy, resTy) =>
          val typedArg = check(ctx, e2, argTy)
          ECBNApp(typedFun, typedArg).withType(resTy)
        case other =>
          fail(s"expected a function, found $other")

    case EBNLam(x, Some(argTy), body, retTy) =>
      WF.check(ctx, argTy)
      val tyBody =
        retTy match
          case Some(t) =>
            WF.check(ctx, t)
            check(ctx + (x -> argTy), body, t)
          case None => infer(ctx + (x -> argTy), body)
      EBNLam(x, Some(argTy), tyBody, tyBody.ty).withType(TFun(argTy, tyBody.ty.get))

    case EBNLam(_, None, _, _) =>
      fail("cannot infer a by-name lambda without a parameter type")

private def subtype(ctx: Ctx, from: Type, to: Type): Expr =
  ctx.constraints.assertStLeq(from.stage, to.stage)
  val coercionTy = TFun(from, to).at()
  (from.base, to.base) match
    case (TInt, TInt) | (TBool, TBool) | (TUnit, TUnit) =>
      val x = Counter.fresh
      val body = ELift(EVar(x).withType(from), to.stage).withType(to)
      ELam(x, None, body, None).withType(coercionTy)
    case (TFun(fromArg, fromRet), TFun(toArg, toRet)) =>
      val argCoercion = subtype(ctx, toArg, fromArg)
      val retCoercion = subtype(ctx, fromRet, toRet)
      ctx.constraints.assertStLeq(to.stage, toArg.stage)
      ctx.constraints.assertStLeq(to.stage, toRet.stage)
      val f = Counter.fresh
      val x = Counter.fresh
      val arg = EApp(argCoercion, EVar(x).withType(toArg), Some(Sta)).withType(fromArg)
      val call = EApp(EVar(f).withType(from), arg, Some(from.stage)).withType(fromRet)
      val body = EApp(retCoercion, call, Some(Sta)).withType(toRet)
      val lam = ELam(x, None, body, None).withType(TFun(toArg, toRet))
      val lifted = ELift(lam, to.stage).withType(to)
      ELam(f, None, lifted, None).withType(coercionTy)
    case _ if ctx.constraints.implyTyEq(from, to) =>
      val x = Counter.fresh
      ELam(x, None, EVar(x).withType(to), None).withType(coercionTy)
    case _ => fail(s"cannot coerce type $from to $to")

private def coerce(ctx: Ctx, expr: Expr, expected: Type): Expr =
  EApp(subtype(ctx, expr.ty.get, expected), expr, Some(Sta)).withType(expected)

private def check(ctx: Ctx, expr: Expr, expected: Type): Expr =
  coerce(ctx, infer(ctx, expr), expected)

private object Subst:
  def constraints(cs: List[StageConstraint], from: String, to: Stage): List[StageConstraint] =
    def subst(st: Stage): Stage = Stage.substitute(st, from, to)
    cs.map(c => StageConstraint(subst(c.lower), subst(c.upper)))

  def expr(e: Expr, from: String, to: Stage): Expr =
    def stage(st: Stage): Stage = Stage.substitute(st, from, to)
    def expr(t: Expr): Expr = Subst.expr(t, from, to)
    def ty(t: Type): Type = Subst.ty(t, from, to)
    val result = e match
      case EUnit | ENum(_) | EBool(_) | EVar(_) | ELoc(_) => e
      case ESLam(s, _, _) if s == from => return e
      case ESLam(s, body, cs) => ESLam(s, expr(body), constraints(cs, from, to))
      case ESApp(t, s) => ESApp(expr(t), stage(s))
      case ELam(x, arg, body, ret) => ELam(x, arg.map(ty), expr(body), ret.map(ty))
      case EBNLam(x, arg, body, ret) => EBNLam(x, arg.map(ty), expr(body), ret.map(ty))
      case EApp(a, b, st) => EApp(expr(a), expr(b), st.map(stage))
      case ELift(t, st) => ELift(expr(t), stage(st))
      case ERun(t) => ERun(expr(t))
      case ELet(x, rhs, body) => ELet(x, expr(rhs), expr(body))
      case ELetRec(x, rhs, body, st) => ELetRec(x, expr(rhs), expr(body), st.map(stage))
      case ECond(c, a, b, st) => ECond(expr(c), expr(a), expr(b), st.map(stage))
      case EBinOp(op, a, b, st) => EBinOp(op, expr(a), expr(b), st.map(stage))
      case EUnaryOp(op, t, st) => EUnaryOp(op, expr(t), st.map(stage))
      case EAlloc(t, st) => EAlloc(expr(t), st.map(stage))
      case EDeref(t, st) => EDeref(expr(t), st.map(stage))
      case EAssign(a, b, st) => EAssign(expr(a), expr(b), st.map(stage))
      case EAscribe(t, tpe) => EAscribe(expr(t), ty(tpe))
      case EIsApp(t) => EIsApp(expr(t))
      case ECBNApp(a, b) => ECBNApp(expr(a), expr(b))
    e.ty.foreach(t => result.withType(ty(t)))
    result

  def ty(tpe: Type, from: String, to: Stage): Type =
    tpe match
      case TUnit | TInt | TBool => tpe
      case TAt(t, st) => TAt(ty(t, from, to), Stage.substitute(st, from, to))
      case TFun(arg, ret) => TFun(ty(arg, from, to), ty(ret, from, to))
      case TRef(t) => TRef(ty(t, from, to))
      case TForallSt(s, _, _) if s == from => tpe
      case TForallSt(s, t, cs) if Stage.variables(to)(s) =>
        val fresh = Counter.fresh
        val renamed = TForallSt(fresh, ty(t, s, SVar(fresh)), constraints(cs, s, SVar(fresh)))
        ty(renamed, from, to)
      case TForallSt(s, t, cs) => TForallSt(s, ty(t, from, to), constraints(cs, from, to))

private def freshenStageBinder(lam: ESLam): Expr =
  val fresh = Counter.fresh
  ESLam(fresh, Subst.expr(lam.body, lam.s, SVar(fresh)),
    Subst.constraints(lam.constraints, lam.s, SVar(fresh)))

private def inferBinOp(op: String, st: Stage): (Type, Type) =
  op match
    case "+" | "-" | "*" | "/" =>
      (TInt.at(st), TInt.at(st))
    case "<=" | ">=" | "<" | ">" | "==" | "!=" =>
      (TInt.at(st), TBool.at(st))
    case _ => fail(s"unsupported binary operator `$op`")

private def inferUnaryOp(op: String, st: Stage): (Type, Type) =
  op match
    case "-" => (TInt.at(st), TInt.at(st))
    case _ => fail(s"unsupported unary operator `$op`")

private def fail(message: String): Nothing =
  throw TypeException(message)

private def assert(cond: Boolean, message: => String): Unit =
  if (!cond) then throw TypeException(message)
