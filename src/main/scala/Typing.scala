package instar.typing

import instar.syntax.*
import Expr.*
import Stage.*
import Type.*

object Counter:
  private var count: Int = 0
  def fresh: String =
    val c = count
    count += 1
    s"$$s$c"

final class TypeException(message: String) extends RuntimeException(message)

private case class Ctx(env: Map[String, Type] = Map(), stEnv: Set[String] = Set()):
  def +(xt: (String, Type)): Ctx = copy(env = env + xt)
  def +(x: String): Ctx = copy(stEnv = stEnv + x)
  def containsVar(x: String): Boolean = env.contains(x)
  def containsStVar(x: String): Boolean = stEnv.contains(x)
  def apply(x: String): Type = env(x)

def infer(expr: Expr): Expr = infer(Ctx(), expr)

def check(expr: Expr, expected: Type): Expr = check(Ctx(), expr, expected)

private def infer(ctx: Ctx, expr: Expr): Expr =
  expr match
    case EUnit => EUnit.withType(TUnit)
    case ENum(i) => ENum(i).withType(TInt)
    case EBool(b) => EBool(b).withType(TBool)

    case EVar(x) =>
      assert(ctx.containsVar(x), s"unbound variable `$x`")
      EVar(x).withType(ctx(x))

    case ELam(x, Some(argTy), body, retTy) =>
      // TODO: check well-formedness of argTy and retTy
      val tyBody =
        retTy match
          case Some(t) => check(ctx + (x -> argTy), body, t)
          case None => infer(ctx + (x -> argTy), body)
      ELam(x, Some(argTy), tyBody, tyBody.ty).withType(TFun(argTy, tyBody.ty.get))

    case ELam(_, None, _, _) =>
      fail("cannot infer a lambda without a parameter type")

    case ESLam(s, body) =>
      val typedBody = infer(ctx + s, body)
      val bodyTy = typedBody.ty.get
      ESLam(s, typedBody).withType(TForallSt(s, bodyTy))

    case ESApp(e, st) =>
      val typedFun = infer(ctx, e)
      val TForallSt(s, bodyTy) = typedFun.ty.get
      ESApp(typedFun, st).withType(substStage(bodyTy, s, st))

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
      val typedInner = infer(ctx, e)
      val innerTy = typedInner.ty.get
      ELift(typedInner, st).withType(wrapAtStage(unliftType(innerTy, st), st))

    case ERun(e) =>
      val typedInner = infer(ctx, e)
      typedInner.ty.get match
        case TCode(t) => ERun(typedInner).withType(t)
        case other => fail(s"`run` expects `Code[T]`, found $other")

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
      val elemTy = typedE.ty.get
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
        case TCode(_) => EIsApp(typedE).withType(TBool)
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

private def check(ctx: Ctx, expr: Expr, expected: Type): Expr =
  expr match
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

    case ESLam(s, body) =>
      expected match
        case TForallSt(s1, bodyTy) =>
          val bodyTy1 = if s == s1 then bodyTy else substStage(bodyTy, s1, SVar(s))
          ESLam(s, check(ctx + s, body, bodyTy1)).withType(expected)
        case other =>
          fail(s"expected a stage-polymorphic type, found $other")

    case other =>
      val typed = infer(ctx, other)
      ensureSame(typed.ty.get, expected)
      typed

private def resolveRecType(ctx: Ctx, expr: Expr): Option[Type] =
  expr match
    case EAscribe(_, ann) => Some(ann)
    case ELam(_, Some(argTy), _, Some(retTy)) =>
      Some(TFun(argTy, retTy))
    case EBNLam(_, Some(argTy), _, Some(retTy)) =>
      Some(TFun(argTy, retTy))
    case ESLam(s, body) =>
      resolveRecType(ctx + s, body).map(TForallSt(s, _))
    case _ =>
      None

private def resolveType(ctx: Ctx, ty: Type): Type =
  ty match
    case TUnit | TInt | TBool => ty
    case TFun(t1, t2) => TFun(resolveType(ctx, t1), resolveType(ctx, t2))
    case TRef(t) => TRef(resolveType(ctx, t))
    case TForallSt(s, t) => TForallSt(s, resolveType(ctx + s, t))
    case TAt(t, s) => TAt(resolveType(ctx, t), s)
    case TCode(t) => TCode(resolveType(ctx, t))

private def substStage(ty: Type, from: String, to: Stage): Type =
  ty match
    case TUnit | TInt | TBool => ty
    case TFun(t1, t2) => TFun(substStage(t1, from, to), substStage(t2, from, to))
    case TRef(t) => TRef(substStage(t, from, to))
    case TForallSt(s, t) if s == from => TForallSt(s, t)
    case TForallSt(s, t) if SVar(s) == to => t
    case TForallSt(s, t) => TForallSt(s, substStage(t, from, to))
    case TAt(t, SVar(s)) if s == from =>
      val t1 = substStage(t, from, to)
      to match
        case SVar(_) => TAt(t1, to)
        case SNum(1) => t1
        case SNum(2) => TCode(t1)
    case TAt(t, SVar(s)) => TAt(substStage(t, from, to), SVar(s))
    case TAt(t, SNum(1)) => substStage(t, from, to)
    case TAt(t, SNum(2)) => TCode(substStage(t, from, to))
    case TCode(t) => TCode(substStage(t, from, to))

private def wrapAtStage(ty: Type, st: Stage): Type =
  st match
    case SNum(1) => ty
    case SNum(2) => TCode(ty)
    case _ => TAt(ty, st)

private def unwrapAtStage(ty: Type, st: Stage): Type =
  (ty, st) match
    case (t, SNum(1)) => t
    case (TCode(t), SNum(2)) => t
    case (TAt(t, s1), s2) if s1 == s2 => t
    case (other, _) => fail(s"type $other is not available at stage $st")

private def unliftType(ty: Type, st: Stage): Type =
  (ty, st) match
    case (t, SNum(1)) => t
    case (TCode(t), SNum(2)) => unliftType(t, st)
    case (TAt(t, s1), s2) if s1 == s2 => unliftType(t, st)
    case (TFun(t1, t2), _) => TFun(unliftType(t1, st), unliftType(t2, st))
    case (TRef(t), _) => TRef(unliftType(t, st))
    case (TForallSt(s, t), _) => TForallSt(s, unliftType(t, st))
    case (other, _) => other

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

private def ensureSame(found: Type, expected: Type): Unit =
  assert(equivType(found, expected), s"type mismatch: found $found, expected $expected")

private def equivType(left: Type, right: Type): Boolean =
  (left, right) match
    case (TUnit, TUnit) | (TInt, TInt) | (TBool, TBool) => true
    case (TFun(l1, l2), TFun(r1, r2)) =>
      equivType(l1, r1) && equivType(l2, r2)
    case (TRef(l), TRef(r)) =>
      equivType(l, r)
    case (TCode(l), TCode(r)) =>
      equivType(l, r)
    case (TAt(t1, st1), TAt(t2, st2)) =>
      equivType(t1, t2) && st1 == st2
    case (TForallSt(x, t1), TForallSt(y, t2)) if x == y =>
      equivType(t1, t2)
    case (TForallSt(x, t1), TForallSt(y, t2)) =>
      val z = Counter.fresh
      equivType(substStage(t1, x, SVar(z)), substStage(t2, y, SVar(z)))
    case _ =>
      false

private def fail(message: String): Nothing =
  throw TypeException(message)
