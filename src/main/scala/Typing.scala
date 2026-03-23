package instar.typing

import instar.syntax.*
import Expr.*
import Stage.*
import Type.*

final class TypeException(message: String) extends RuntimeException(message)

private case class Ctx(env: Map[String, Type] = Map(), stEnv: Map[String, Stage] = Map()):
  def bindTerm(x: String, ty: Type): Ctx = copy(env = env + (x -> ty))
  def bindStage(x: String): Ctx = copy(stEnv = stEnv - x) // FIXME: this doesn't look right, need to handle name shadowing properly
  def bindStage(x: String, st: Stage): Ctx = copy(stEnv = stEnv + (x -> st))

def infer(expr: Expr): Expr = infer(Ctx(), expr)

def check(expr: Expr, expected: Type): Expr = check(Ctx(), expr, expected)

private def infer(ctx: Ctx, expr: Expr): Expr =
  expr match
    case EUnit => EUnit.withType(TUnit)
    case ENum(i) => ENum(i).withType(TInt)
    case EBool(b) => EBool(b).withType(TBool)

    case EVar(x) =>
      EVar(x).withType(ctx.env.getOrElse(x, fail(s"unbound variable `$x`")))

    case ELam(x, Some(argTy), body, retTy) =>
      val arg = resolveType(ctx, argTy)
      val typedBody =
        retTy match
          case Some(t) => check(ctx.bindTerm(x, arg), body, resolveType(ctx, t))
          case None => infer(ctx.bindTerm(x, arg), body)
      val bodyTy = typedBody.ty.getOrElse(fail("internal error: lambda body is missing a type"))
      ELam(x, Some(arg), typedBody, Some(bodyTy)).withType(TFun(arg, bodyTy))

    case ELam(_, None, _, _) =>
      fail("cannot infer a lambda without a parameter type")

    case EBNLam(x, Some(argTy), body, retTy) =>
      val arg = resolveType(ctx, argTy)
      val typedBody =
        retTy match
          case Some(t) => check(ctx.bindTerm(x, arg), body, resolveType(ctx, t))
          case None => infer(ctx.bindTerm(x, arg), body)
      val bodyTy = typedBody.ty.getOrElse(fail("internal error: by-name lambda body is missing a type"))
      EBNLam(x, Some(arg), typedBody, Some(bodyTy)).withType(TFun(arg, bodyTy))

    case EBNLam(_, None, _, _) =>
      fail("cannot infer a by-name lambda without a parameter type")

    case ESLam(s, body) =>
      val typedBody = infer(ctx.bindStage(s), body)
      val bodyTy = typedBody.ty.getOrElse(fail("internal error: stage lambda body is missing a type"))
      ESLam(s, typedBody).withType(TForallSt(s, bodyTy))

    case ESApp(e, st) =>
      val typedFun = infer(ctx, e)
      typedFun.ty.getOrElse(fail("internal error: stage application head is missing a type")) match
        case TForallSt(s, bodyTy) =>
          val st1 = resolveStage(ctx, st)
          ESApp(typedFun, st1).withType(substStage(bodyTy, s, st1))
        case other =>
          fail(s"expected a stage-polymorphic expression, found $other")

    case EApp(e1, e2, st) =>
      val st1 = resolveExprStage(ctx, st)
      val typedFun = infer(ctx, e1)
      unwrapAtStage(
        typedFun.ty.getOrElse(fail("internal error: application head is missing a type")),
        st1,
      ) match
        case TFun(argTy, resTy) =>
          val typedArg = check(ctx, e2, wrapAtStage(argTy, st1))
          EApp(typedFun, typedArg, Some(st1)).withType(wrapAtStage(resTy, st1))
        case other =>
          fail(s"expected a function, found $other")

    case ECBNApp(e1, e2) =>
      val typedFun = infer(ctx, e1)
      typedFun.ty.getOrElse(fail("internal error: call-by-name application head is missing a type")) match
        case TFun(argTy, resTy) =>
          val typedArg = check(ctx, e2, argTy)
          ECBNApp(typedFun, typedArg).withType(resTy)
        case other =>
          fail(s"expected a function, found $other")

    case ELift(e, st) =>
      val st1 = resolveStage(ctx, st)
      val typedInner = infer(ctx, e)
      val innerTy = typedInner.ty.getOrElse(fail("internal error: lifted expression is missing a type"))
      ELift(typedInner, st1).withType(wrapAtStage(unliftType(innerTy, st1), st1))

    case ERun(e) =>
      val typedInner = infer(ctx, e)
      typedInner.ty.getOrElse(fail("internal error: run argument is missing a type")) match
        case TCode(t) => ERun(typedInner).withType(t)
        case other => fail(s"`run` expects `Code[T]`, found $other")

    case ELet(x, rhs, body) =>
      val typedRhs = infer(ctx, rhs)
      val rhsTy = typedRhs.ty.getOrElse(fail("internal error: let rhs is missing a type"))
      val typedBody = infer(ctx.bindTerm(x, rhsTy), body)
      ELet(x, typedRhs, typedBody).withType(typedBody.ty.getOrElse(fail("internal error: let body is missing a type")))

    case ELetRec(f, rhs, body) =>
      val recTy = recursiveType(ctx, rhs)
      val typedRhs =
        if rhs.freeVar.contains(f) then
          recTy match
            case Some(t) => check(ctx.bindTerm(f, t), rhs, t)
            case None => fail(s"recursive `letrec` binding `$f` needs an annotation")
        else infer(ctx, rhs)
      val rhsTy = typedRhs.ty.getOrElse(fail("internal error: letrec rhs is missing a type"))
      val typedBody = infer(ctx.bindTerm(f, rhsTy), body)
      ELetRec(f, typedRhs, typedBody).withType(typedBody.ty.getOrElse(fail("internal error: letrec body is missing a type")))

    case ECond(e1, e2, e3, st) =>
      val st1 = resolveExprStage(ctx, st)
      val typedCond = check(ctx, e1, wrapAtStage(TBool, st1))
      val typedThen = infer(ctx, e2)
      val thenTy = typedThen.ty.getOrElse(fail("internal error: then branch is missing a type"))
      val typedElse = check(ctx, e3, thenTy)
      ECond(typedCond, typedThen, typedElse, Some(st1)).withType(thenTy)

    case EBinOp(op, e1, e2, st) =>
      val st1 = resolveExprStage(ctx, st)
      val (argTy, resTy) = inferBinOp(op, st1)
      val typedL = check(ctx, e1, argTy)
      val typedR = check(ctx, e2, argTy)
      EBinOp(op, typedL, typedR, Some(st1)).withType(resTy)

    case EUnaryOp(op, e, st) =>
      val st1 = resolveExprStage(ctx, st)
      val (argTy, resTy) = inferUnaryOp(op, st1)
      val typedE = check(ctx, e, argTy)
      EUnaryOp(op, typedE, Some(st1)).withType(resTy)

    case EAlloc(e, st) =>
      val st1 = resolveExprStage(ctx, st)
      val typedE = infer(ctx, e)
      val elemTy = unwrapAtStage(typedE.ty.getOrElse(fail("internal error: ref argument is missing a type")), st1)
      EAlloc(check(ctx, e, wrapAtStage(elemTy, st1)), Some(st1)).withType(wrapAtStage(TRef(elemTy), st1))

    case EDeref(e, st) =>
      val st1 = resolveExprStage(ctx, st)
      val typedE = infer(ctx, e)
      unwrapAtStage(typedE.ty.getOrElse(fail("internal error: deref argument is missing a type")), st1) match
        case TRef(elemTy) =>
          EDeref(check(ctx, e, wrapAtStage(TRef(elemTy), st1)), Some(st1)).withType(wrapAtStage(elemTy, st1))
        case other =>
          fail(s"`!` expects a reference, found $other")

    case EAssign(e1, e2, st) =>
      val st1 = resolveExprStage(ctx, st)
      val typedL = infer(ctx, e1)
      unwrapAtStage(typedL.ty.getOrElse(fail("internal error: assignment lhs is missing a type")), st1) match
        case TRef(elemTy) =>
          val lhs1 = check(ctx, e1, wrapAtStage(TRef(elemTy), st1))
          val rhs1 = check(ctx, e2, wrapAtStage(elemTy, st1))
          EAssign(lhs1, rhs1, Some(st1)).withType(wrapAtStage(TUnit, st1))
        case other =>
          fail(s"`:=` expects a reference on the left, found $other")

    case EAscribe(e, asTy) =>
      val ty = resolveType(ctx, asTy)
      EAscribe(check(ctx, e, ty), ty).withType(ty)

    case EFix(f, e, st) =>
      val st1 = resolveExprStage(ctx, st)
      val recTy = recursiveType(ctx, e)
      val typedBody =
        if e.freeVar.contains(f) then
          recTy match
            case Some(t) => check(ctx.bindTerm(f, t), e, t)
            case None => fail(s"recursive `fix` binding `$f` needs an annotation")
        else infer(ctx, e)
      val bodyTy = typedBody.ty.getOrElse(fail("internal error: fix body is missing a type"))
      EFix(f, typedBody, Some(st1)).withType(bodyTy)

    case EIsApp(e) =>
      val typedE = infer(ctx, e)
      typedE.ty.getOrElse(fail("internal error: isApp argument is missing a type")) match
        case TCode(_) => EIsApp(typedE).withType(TBool)
        case other => fail(s"`isApp` expects `Code[T]`, found $other")

    case ELoc(_) =>
      fail("cannot type-check internal location expressions")

private def check(ctx: Ctx, expr: Expr, expected: Type): Expr =
  val expected1 = normalizeType(resolveType(ctx, expected))
  expr match
    case ELam(x, argTy, body, _) =>
      expected1 match
        case TFun(argTy1, retTy1) =>
          argTy.foreach(t => ensureSame(resolveType(ctx, t), argTy1))
          val typedBody = check(ctx.bindTerm(x, argTy1), body, retTy1)
          ELam(x, Some(argTy1), typedBody, Some(retTy1)).withType(expected1)
        case other =>
          fail(s"expected a function type, found $other")

    case EBNLam(x, argTy, body, _) =>
      expected1 match
        case TFun(argTy1, retTy1) =>
          argTy.foreach(t => ensureSame(resolveType(ctx, t), argTy1))
          val typedBody = check(ctx.bindTerm(x, argTy1), body, retTy1)
          EBNLam(x, Some(argTy1), typedBody, Some(retTy1)).withType(expected1)
        case other =>
          fail(s"expected a function type, found $other")

    case ESLam(s, body) =>
      expected1 match
        case TForallSt(s1, bodyTy) =>
          val bodyTy1 = if s == s1 then bodyTy else substStage(bodyTy, s1, SVar(s))
          ESLam(s, check(ctx.bindStage(s), body, bodyTy1)).withType(expected1)
        case other =>
          fail(s"expected a stage-polymorphic type, found $other")

    case other =>
      val typed = infer(ctx, other)
      ensureSame(typed.ty.getOrElse(fail("internal error: expression is missing a type")), expected1)
      typed

private def recursiveType(ctx: Ctx, expr: Expr): Option[Type] =
  expr match
    case EAscribe(_, ann) => Some(resolveType(ctx, ann))
    case ELam(_, Some(argTy), _, Some(retTy)) =>
      Some(TFun(resolveType(ctx, argTy), resolveType(ctx, retTy)))
    case EBNLam(_, Some(argTy), _, Some(retTy)) =>
      Some(TFun(resolveType(ctx, argTy), resolveType(ctx, retTy)))
    case ESLam(s, body) =>
      recursiveType(ctx.bindStage(s), body).map(TForallSt(s, _))
    case _ =>
      None

private def resolveExprStage(ctx: Ctx, st: Option[Stage]): Stage =
  st match
    case Some(stage) => resolveStage(ctx, stage)
    case None => Sta

private def resolveStage(ctx: Ctx, st: Stage): Stage =
  st match
    case SVar(x) => ctx.stEnv.getOrElse(x, st)
    case SNum(1) | SNum(2) => st
    case SNum(n) => fail(s"unsupported stage `$n`")

private def resolveType(ctx: Ctx, ty: Type): Type =
  normalizeType {
    ty match
      case TUnit | TInt | TBool => ty
      case TFun(t1, t2) => TFun(resolveType(ctx, t1), resolveType(ctx, t2))
      case TRef(t) => TRef(resolveType(ctx, t))
      case TForallSt(s, t) => TForallSt(s, resolveType(ctx.bindStage(s), t))
      case TAt(t, s) => TAt(resolveType(ctx, t), resolveStage(ctx, s))
      case TCode(t) => TCode(resolveType(ctx, t))
  }

private def normalizeType(ty: Type): Type =
  ty match
    case TUnit | TInt | TBool => ty
    case TFun(t1, t2) => TFun(normalizeType(t1), normalizeType(t2))
    case TRef(t) => TRef(normalizeType(t))
    case TForallSt(s, t) => TForallSt(s, normalizeType(t))
    case TAt(t, SNum(1)) => normalizeType(t)
    case TAt(t, SNum(2)) => TCode(normalizeType(t))
    case TAt(t, s) => TAt(normalizeType(t), s)
    case TCode(t) => TCode(normalizeType(t))

private def substStage(ty: Type, from: String, to: Stage): Type =
  normalizeType {
    ty match
      case TUnit | TInt | TBool => ty
      case TFun(t1, t2) => TFun(substStage(t1, from, to), substStage(t2, from, to))
      case TRef(t) => TRef(substStage(t, from, to))
      case TForallSt(s, t) if s == from => TForallSt(s, t)
      case TForallSt(s, t) => TForallSt(s, substStage(t, from, to))
      case TAt(t, SVar(s)) if s == from => TAt(substStage(t, from, to), to)
      case TAt(t, s) => TAt(substStage(t, from, to), s)
      case TCode(t) => TCode(substStage(t, from, to))
  }

private def wrapAtStage(ty: Type, st: Stage): Type =
  normalizeType {
    st match
      case SNum(1) => ty
      case SNum(2) => TCode(ty)
      case _ => TAt(ty, st)
  }

private def unwrapAtStage(ty: Type, st: Stage): Type =
  (normalizeType(ty), st) match
    case (t, SNum(1)) => t
    case (TCode(t), SNum(2)) => t
    case (TAt(t, s1), s2) if s1 == s2 => t
    case (other, _) => fail(s"type $other is not available at stage $st")

private def unliftType(ty: Type, st: Stage): Type =
  normalizeType {
    (normalizeType(ty), st) match
      case (t, SNum(1)) => t
      case (TCode(t), SNum(2)) => unliftType(t, st)
      case (TAt(t, s1), s2) if s1 == s2 => unliftType(t, st)
      case (TFun(t1, t2), _) => TFun(unliftType(t1, st), unliftType(t2, st))
      case (TRef(t), _) => TRef(unliftType(t, st))
      case (TForallSt(s, t), _) => TForallSt(s, unliftType(t, st))
      case (other, _) => other
  }

private def inferBinOp(op: String, st: Stage): (Type, Type) =
  op match
    case "+" | "-" | "*" | "/" => (wrapAtStage(TInt, st), wrapAtStage(TInt, st))
    case "<=" | ">=" | "<" | ">" | "==" | "!=" => (wrapAtStage(TInt, st), wrapAtStage(TBool, st))
    case _ => fail(s"unsupported binary operator `$op`")

private def inferUnaryOp(op: String, st: Stage): (Type, Type) =
  op match
    case "-" => (wrapAtStage(TInt, st), wrapAtStage(TInt, st))
    case _ => fail(s"unsupported unary operator `$op`")

private def ensureSame(found: Type, expected: Type): Unit =
  if normalizeType(found) != normalizeType(expected) then
    fail(s"type mismatch: found ${normalizeType(found)}, expected ${normalizeType(expected)}")

private def fail(message: String): Nothing =
  throw TypeException(message)
