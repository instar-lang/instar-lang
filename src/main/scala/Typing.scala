package instar.typing

import instar.Config
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
      case TRef(inner) => check(ctx, inner)
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

type ⇀[A, B] = PartialFunction[A, B]

private def inferElab: (Ctx, Expr) ⇀ Expr =
  case (ctx, EApp(e1, e2, None)) =>
    val typedFun = infer(ctx, e1)
    val st = stageOf(typedFun.ty.get)
    unwrapAtStage(typedFun.ty.get, st) match
      case TFun(argTy, resTy) =>
        val typedArg = check(ctx, e2, wrapAtStage(argTy, st))
        EApp(typedFun, typedArg, Some(st)).withType(wrapAtStage(resTy, st))
      case other =>
        fail(s"expected a function, found $other")
  case (ctx, EBinOp(op, e1, e2, None)) =>
    val typedL = infer(ctx, e1)
    val typedR = infer(ctx, e2)
    // Here we assume/require e1 and e2 are at the same stage
    val st = stageOf(typedL.ty.get, typedR.ty.get)
    val (argTy, resTy) = inferBinOp(op, st)
    ensureSame(typedL.ty.get, argTy, Some(typedL))
    ensureSame(typedR.ty.get, argTy, Some(typedR))
    EBinOp(op, typedL, typedR, Some(st)).withType(resTy)
  case (ctx, EBinOp(op, e1, e2, None)) =>
    ???

private def infer(ctx: Ctx, expr: Expr): Expr =
  if Config.elab && inferElab.isDefinedAt((ctx, expr)) then
    inferElab((ctx, expr))
  else expr match
    case EUnit => EUnit.withType(TUnit)
    case ENum(i) => ENum(i).withType(TInt)
    case EBool(b) => EBool(b).withType(TBool)

    case EVar(x) =>
      assert(ctx.containsVar(x), s"unbound variable `$x`")
      EVar(x).withType(ctx(x))

    case ELam(x, Some(argTy), body, retTy) =>
      WF.check(ctx, argTy)
      retTy.foreach(t => WF.check(ctx, t))
      val tyBody =
        retTy match
          case Some(t) => check(ctx + (x -> argTy), body, t)
          case None => infer(ctx + (x -> argTy), body)
      ELam(x, Some(argTy), tyBody, tyBody.ty).withType(TFun(argTy, tyBody.ty.get))

    case ELam(_, None, _, _) =>
      fail("cannot infer a lambda without a parameter type")

    case lam: ESLam if ctx.containsStVar(lam.s) =>
      infer(ctx, freshenStageBinder(lam))
    case ESLam(s, body, cs) =>
      val typedBody = infer(ctx + (s, cs), body)
      val bodyTy = typedBody.ty.get
      ESLam(s, typedBody, cs).withType(TForallSt(s, bodyTy, cs))

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

    case EApp(e1, e2, None) => infer(ctx, EApp(e1, e2, Some(Sta)))

    case EApp(e1, e2, Some(st)) =>
      val typedFun = infer(ctx, e1)
      unwrapAtStage(typedFun.ty.get, st) match
        case TFun(argTy, resTy) =>
          val typedArg = check(ctx, e2, wrapAtStage(argTy, st))
          EApp(typedFun, typedArg, Some(st)).withType(wrapAtStage(resTy, st))
        case other =>
          fail(s"expected a function, found $other")

    case ELift(e, st) =>
      val typed = infer(ctx, e)
      val ty = typed.ty.get
      if ty.stage == Dyn && st == Dyn then fail("cannot lift code values")
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
      val typedInner = infer(ctx, e)
      val ty = typedInner.ty.get
      if ty.stage == Dyn then ERun(typedInner).withType(ty.erase)
      else fail(s"`run` expects `Code[T]`, found $ty")

    case ELet(x, rhs, body) =>
      val typedRhs = infer(ctx, rhs)
      val typedBody = infer(ctx + (x -> typedRhs.ty.get), body)
      ELet(x, typedRhs, typedBody).withType(typedBody.ty.get)

    case ELetRec(f, rhs, body) =>
      val recTy = resolveRecType(ctx, rhs)
      val typedRhs = recTy match
        case Some(t) => check(ctx + (f -> t), rhs, t)
        case None => fail(s"recursive `letrec` binding `$f` needs an annotation")
      val rhsTy = typedRhs.ty.get
      val typedBody = infer(ctx + (f -> rhsTy), body)
      ELetRec(f, typedRhs, typedBody).withType(typedBody.ty.get)

    case ECond(e1, e2, e3, None) => infer(ctx, ECond(e1, e2, e3, Some(Sta)))

    case ECond(e1, e2, e3, Some(st)) =>
      val typedCond = check(ctx, e1, wrapAtStage(TBool, st))
      val typedThen = infer(ctx, e2)
      val thenTy = typedThen.ty.get
      val typedElse = check(ctx, e3, thenTy)
      ECond(typedCond, typedThen, typedElse, Some(st)).withType(thenTy)

    case EBinOp(op, e1, e2, None) => infer(ctx, EBinOp(op, e1, e2, Some(Sta)))

    case EBinOp(op, e1, e2, Some(st)) =>
      val (argTy, resTy) = inferBinOp(op, st)
      val typedL = check(ctx, e1, argTy)
      val typedR = check(ctx, e2, argTy)
      EBinOp(op, typedL, typedR, Some(st)).withType(resTy)

    case EUnaryOp(op, e, None) => infer(ctx, EUnaryOp(op, e, Some(Sta)))

    case EUnaryOp(op, e, Some(st)) =>
      val (argTy, resTy) = inferUnaryOp(op, st)
      val typedE = check(ctx, e, argTy)
      EUnaryOp(op, typedE, Some(st)).withType(resTy)

    case EAlloc(e, None) => infer(ctx, EAlloc(e, Some(Sta)))

    case EAlloc(e, Some(st)) =>
      val typedE = infer(ctx, e)
      // FIXME: we cannot have EAlloc(code, SNum(2))
      val elemTy = unwrapAtStage(typedE.ty.get, st)
      EAlloc(typedE, Some(st)).withType(wrapAtStage(TRef(elemTy), st))

    case EDeref(e, None) => infer(ctx, EDeref(e, Some(Sta)))

    case EDeref(e, Some(st)) =>
      val typedE = infer(ctx, e)
      unwrapAtStage(typedE.ty.get, st) match
        case TRef(elemTy) =>
          EDeref(typedE, Some(st)).withType(wrapAtStage(elemTy, st))
        case other =>
          fail(s"`!` expects a reference, found $other")

    case EAssign(e1, e2, None) => infer(ctx, EAssign(e1, e2, Some(Sta)))

    case EAssign(e1, e2, Some(st)) =>
      val typedL = infer(ctx, e1)
      unwrapAtStage(typedL.ty.get, st) match
        case TRef(elemTy) =>
          val typedR = check(ctx, e2, wrapAtStage(elemTy, st))
          EAssign(typedL, typedR, Some(st)).withType(wrapAtStage(TUnit, st))
        case other =>
          fail(s"`:=` expects a reference on the left, found $other")

    case EAscribe(e, ty) =>
      EAscribe(check(ctx, e, ty), ty).withType(ty)

    case EFix(f, e, None) => infer(ctx, EFix(f, e, Some(Sta)))
    case EFix(f, e, Some(st)) =>
      val recTy = resolveRecType(ctx, e)
      val typedBody = recTy match
        case Some(t) => check(ctx + (f -> t), e, t)
        case None => fail(s"recursive `fix` binding `$f` needs an annotation")
      EFix(f, typedBody, Some(st)).withType(typedBody.ty.get)

    case ELoc(_) =>
      fail("cannot type-check internal location expressions")

    // Experimental:

    case EIsApp(e) =>
      val typedE = infer(ctx, e)
      typedE.ty.getOrElse(fail("internal error: isApp argument is missing a type")) match
        case ty if ty.stage == Dyn => EIsApp(typedE).withType(TBool)
        case other => fail(s"`isApp` expects `Code[T]`, found $other")

    case ECBNApp(e1, e2) =>
      val typedFun = infer(ctx, e1)
      typedFun.ty.getOrElse(fail("internal error: call-by-name application head is missing a type")) match
        case TFun(argTy, resTy) =>
          val typedArg = check(ctx, e2, argTy)
          ECBNApp(typedFun, typedArg).withType(resTy)
        case other =>
          fail(s"expected a function, found $other")

    case EBNLam(x, Some(argTy), body, retTy) =>
      val tyBody =
        retTy match
          case Some(t) => check(ctx + (x -> argTy), body, t)
          case None => infer(ctx + (x -> argTy), body)
      EBNLam(x, Some(argTy), tyBody, tyBody.ty).withType(TFun(argTy, tyBody.ty.get))

    case EBNLam(_, None, _, _) =>
      fail("cannot infer a by-name lambda without a parameter type")

def coerce(e: Expr, t1: Type, to: Type): Expr =
  if equivType(t1, to) then e
  else if equivType(t1.at(Sta), to.at(Sta)) then ELift(e, to.stage).withType(to)
  else fail(s"cannot coerce type $t1 to $to")

private def checkElab: PartialFunction[(Ctx, Expr, Type), Expr] =
  case (ctx, EUnit, expected) =>
    coerce(EUnit.withType(TUnit), TUnit, expected)
  case (ctx, ENum(i), expected) =>
    coerce(ENum(i).withType(TInt), TInt, expected)
  case (ctx, EBool(b), expected) =>
    coerce(EBool(b).withType(TBool), TBool, expected)
  case (ctx, EVar(x), expected) =>
    assert(ctx.containsVar(x), s"unbound variable `$x`")
    coerce(EVar(x).withType(ctx(x)), ctx(x), expected)
  case (ctx, ECond(e1, e2, e3, None), expected) =>
    val typedCond = infer(ctx, e1)
    typedCond.ty.get match
      case TBool =>
        val typedThen = check(ctx, e2, expected)
        val typedElse = check(ctx, e3, expected)
        ECond(typedCond, typedThen, typedElse, Some(SNum(1))).withType(expected)
      case TAt(TBool, SNum(2)) =>
        expected match
          case TAt(_, SNum(2)) =>
            val typedThen = check(ctx, e2, expected)
            val typedElse = check(ctx, e3, expected)
            ECond(typedCond, typedThen, typedElse, Some(SNum(2))).withType(expected)
          case _ => fail(s"expected a code type for ECond, found $expected")
      case TAt(TBool, st) =>
        ???
  case (ctx, EBinOp(op, e1, e2, None), expected) =>
    val (argTy, resTy) = inferBinOp(op, stageOf(expected))
    val typedL = check(ctx, e1, argTy)
    val typedR = check(ctx, e2, argTy)
    EBinOp(op, typedL, typedR, Some(stageOf(expected))).withType(resTy)

private def check(ctx: Ctx, expr: Expr, expected: Type): Expr =
  if Config.elab && checkElab.isDefinedAt((ctx, expr, expected)) then
    checkElab((ctx, expr, expected))
  else expr match
    case ELam(x, argTy, body, retTy) =>
      expected match
        case TFun(argTy1, retTy1) =>
          argTy.map(t => ensureSame(t, argTy1))
          retTy.map(t => ensureSame(t, retTy1))
          val typedBody = check(ctx + (x -> argTy1), body, retTy1)
          ELam(x, Some(argTy1), typedBody, Some(retTy1)).withType(expected)
        case other =>
          fail(s"expected a function type, found $other")

    case EBNLam(x, argTy, body, retTy) =>
      expected match
        case TFun(argTy1, retTy1) =>
          argTy.map(t => ensureSame(t, argTy1))
          retTy.map(t => ensureSame(t, retTy1))
          val typedBody = check(ctx + (x -> argTy1), body, retTy1)
          ELam(x, Some(argTy1), typedBody, Some(retTy1)).withType(expected)
        case other =>
          fail(s"expected a function type, found $other")

    case ESLam(s, body, cs) =>
      expected match
        case TForallSt(s1, bodyTy, _) =>
          val bodyTy1 = if s == s1 then bodyTy else substStage(bodyTy, s1, SVar(s))
          ESLam(s, check(ctx + (s, cs), body, bodyTy1), cs).withType(expected)
        case other =>
          fail(s"expected a stage-polymorphic type, found $other")

    case other =>
      val typed = infer(ctx, other)
      ensureSame(typed.ty.get, expected)
      typed

// XXX: the ctx seems not necessary
private def resolveRecType(ctx: Ctx, expr: Expr): Option[Type] =
  expr match
    case EAscribe(_, ann) => Some(ann)
    case ELift(e, st) =>
      resolveRecType(ctx, e) match
        case Some(t) => Some(t.at(st))
        case None => None
    case ELam(_, Some(argTy), _, Some(retTy)) =>
      Some(TFun(argTy, retTy))
    case ELam(x, Some(argTy), body, None) =>
      resolveRecType(ctx + (x -> argTy), body) match
        case Some(retTy) => Some(TFun(argTy, retTy))
        case None => None
    case EBNLam(_, Some(argTy), _, Some(retTy)) =>
      Some(TFun(argTy, retTy))
    case EBNLam(x, Some(argTy), body, None) =>
      resolveRecType(ctx + (x -> argTy), body) match
        case Some(retTy) => Some(TFun(argTy, retTy))
        case None => None
    case ESLam(s, body, cs) =>
      resolveRecType(ctx + (s, cs), body).map(TForallSt(s, _, cs))
    case _ =>
      None

private def substStage(ty: Type, from: String, to: Stage): Type =
  Subst.ty(ty, from, to)

private def stageOf(ty: Type): Stage = ty.stage

private def stageOf(ty1: Type, ty2: Type): Stage =
  if ty1.stage == ty2.stage then ty1.stage else Sta

private def wrapAtStage(ty: Type, st: Stage): Type =
  if st == Sta then ty else ty.at(st)

private def unwrapAtStage(ty: Type, st: Stage): Type =
  if st == Sta then ty
  else if ty.stage == st then ty.base
  else fail(s"type $ty is not available at stage $st")

private def inferBinOp(op: String, st: Stage): (Type, Type) =
  op match
    case "+" | "-" | "*" | "/" =>
      (wrapAtStage(TInt, st), wrapAtStage(TInt, st))
    case "<=" | ">=" | "<" | ">" | "==" | "!=" =>
      (wrapAtStage(TInt, st), wrapAtStage(TBool, st))
    case _ => fail(s"unsupported binary operator `$op`")

private def inferUnaryOp(op: String, st: Stage): (Type, Type) =
  op match
    case "-" => (wrapAtStage(TInt, st), wrapAtStage(TInt, st))
    case _ => fail(s"unsupported unary operator `$op`")

private def ensureSame(found: Type, expected: Type, expr: Option[Expr] = None): Unit =
  assert(equivType(found, expected), s"type mismatch: found $found, expected $expected, expr: $expr")

private def equivType(left: Type, right: Type): Boolean =
  Nil.implyTyEq(left, right)

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
      case ELetRec(x, rhs, body) => ELetRec(x, expr(rhs), expr(body))
      case EFix(x, body, st) => EFix(x, expr(body), st.map(stage))
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

private def fail(message: String): Nothing =
  throw TypeException(message)

private def assert(cond: Boolean, message: => String): Unit =
  if (!cond) then throw TypeException(message)