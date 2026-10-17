package instar.syntax

import scala.language.implicitConversions

enum Stage:
  case SNum(n: Int)
  case SVar(x: String)
  case SJoin(left: Stage, right: Stage)

  def |(other: Stage): Stage = SJoin(this, other)

object Stage:
  def variables(stage: Stage): Set[String] = stage match
    case SNum(_) => Set.empty
    case SVar(name) => Set(name)
    case SJoin(a, b) => variables(a) ++ variables(b)

  def simplify(stage: Stage): Stage =
    def terms(s: Stage): List[Stage] = s match
      case SJoin(a, b) => terms(a) ++ terms(b)
      case other => List(other)
    val parts = terms(stage)
    if parts.contains(SNum(2)) then SNum(2)
    else
      val remaining = parts.filterNot(_ == SNum(1)).distinct.sortBy {
        case SVar(name) => (1, name)
        case SNum(n) => (0, n.toString)
        case _: SJoin => (2, "")
      }
      remaining.reduceOption(SJoin(_, _)).getOrElse(SNum(1))

  def join(a: Stage, b: Stage): Stage = simplify(SJoin(a, b))

  def substitute(stage: Stage, from: String, to: Stage): Stage = stage match
    case SVar(name) if name == from => to
    case SJoin(a, b) => SJoin(substitute(a, from, to), substitute(b, from, to))
    case other => other

case class StageConstraint(lower: Stage, upper: Stage)

enum Type:
  case TUnit, TInt, TBool
  case TFun(t1: Type, t2: Type)
  case TRef(t: Type)
  case TForallSt(s: String, t: Type, constraints: List[StageConstraint] = Nil)
  case TAt(t: Type, s: Stage)

  def stage: Stage = this match
    case TAt(_, s) => s
    case _ => Sta

  def base: Type = this match
    case TAt(t, _) => t.base
    case t => t

  def at(target: Stage = stage): Type =
    val t = base
    if target == t.stage then t else TAt(t, target)

  def erase: Type = base match
    case TFun(arg, ret) => TFun(arg.erase, ret.erase)
    case TRef(inner) => TRef(inner.erase)
    case t => t

type Loc = Int

enum Expr:
  var ty: Option[Type] = None
  def withType(t: Type): Expr = { ty = Some(t); this }
  case EUnit
  case ENum(i: Int)
  case EBool(b: Boolean)
  case EVar(name: String)
  case ESLam(s: String, body: Expr, constraints: List[StageConstraint] = Nil)
  case ESApp(e: Expr, st: Stage)
  case ELam(x: String, argTy: Option[Type], body: Expr, retTy: Option[Type])
  case EBNLam(x: String, argTy: Option[Type], body: Expr, retTy: Option[Type])
  case EApp(e1: Expr, e2: Expr, st: Option[Stage])
  case ELift(t: Expr, to: Stage)
  case ERun(t: Expr)
  case ELet(x: String, rhs: Expr, body: Expr)
  case ELetRec(f: String, rhs: Expr, body: Expr, st: Option[Stage] = None)
  case ECond(e1: Expr, e2: Expr, e3: Expr, st: Option[Stage])
  case EBinOp(op: String, e1: Expr, e2: Expr, st: Option[Stage])
  case EUnaryOp(op: String, e: Expr, st: Option[Stage])
  case EAlloc(e: Expr, st: Option[Stage])
  case EDeref(e: Expr, st: Option[Stage])
  case EAssign(e1: Expr, e2: Expr, st: Option[Stage])
  case EAscribe(e: Expr, asTy: Type)
  // Experimental:
  case ELoc(l: Loc)
  // Extend the language to allow programmers to inspect code values
  case EIsApp(e: Expr)
  case ECBNApp(e1: Expr, e2: Expr)

val Sta = Stage.SNum(1)
val Dyn = Stage.SNum(2)

extension (e: Expr)
  def isPure: Boolean =
    e match
      case EUnit | ENum(_) | EBool(_) | EVar(_) => true
      case ESLam(_, _, _) | ELam(_, _, _, _) | EBNLam(_, _, _, _) => true
      case EBinOp(_, _, _, _) | EUnaryOp(_, _, _) => true
      case ESApp(_, _) | EApp(_, _, _) => false
      case ELift(t, _) => false
      case EAlloc(_, _) | EDeref(_, _) | EAssign(_, _, _) => false
      case ERun(t) => t.isPure
      case ELet(_, rhs, body) => rhs.isPure && body.isPure
      case ELetRec(_, rhs, body, _) => rhs.isPure && body.isPure
      case ECond(e1, e2, e3, _) => e1.isPure && e2.isPure && e3.isPure
      case EAscribe(e, _) => e.isPure
      case _ => false

  def freeVar: Set[String] =
    e match
      case EUnit | ENum(_) | EBool(_) | ELoc(_) => Set()
      case EVar(x) => Set(x)
      case ESLam(s, body, _) => body.freeVar
      case ESApp(e, _) => e.freeVar
      case ELam(x, _, body, _) => body.freeVar - x
      case EBNLam(x, _, body, _) => body.freeVar - x
      case EApp(e1, e2, _) => e1.freeVar ++ e2.freeVar
      case ECBNApp(e1, e2) => e1.freeVar ++ e2.freeVar
      case ELift(t, _) => t.freeVar
      case ERun(t) => t.freeVar
      case ELet(x, rhs, body) => rhs.freeVar ++ (body.freeVar - x)
      case ELetRec(f, rhs, body, _) => (rhs.freeVar - f) ++ (body.freeVar - f)
      case ECond(e1, e2, e3, _) => e1.freeVar ++ e2.freeVar ++ e3.freeVar
      case EBinOp(_, e1, e2, _) => e1.freeVar ++ e2.freeVar
      case EUnaryOp(_, e, _) => e.freeVar
      case EAlloc(e, _) => e.freeVar
      case EDeref(e, _) => e.freeVar
      case EAssign(e1, e2, _) => e1.freeVar ++ e2.freeVar
      case EAscribe(e, _) => e.freeVar
      case EIsApp(e) => e.freeVar

  // We only use this function to substitute the binding variable with the argument (which is always a pure, atomic expression),
  // and all variables after reflect are distinct, so we do not need to consider variable capture here.
  def subst(from: String, to: Expr): Expr =
    e match
      case EUnit | ENum(_) | EBool(_) => e
      case EVar(x) => if x == from then to else e
      case ESLam(s, body, constraints) => ESLam(s, body.subst(from, to), constraints)
      case ESApp(e, st) => ESApp(e.subst(from, to), st)
      case ELam(x, argTy, body, retTy) =>
        ELam(x, argTy, body.subst(from, to), retTy)
      case EApp(e1, e2, st) => EApp(e1.subst(from, to), e2.subst(from, to), st)
      case ELift(t, s) => ELift(t.subst(from, to), s)
      case ERun(t) => ERun(t.subst(from, to))
      case ELet(x, rhs, body) =>
        ELet(x, rhs.subst(from, to), body.subst(from, to))
      case ELetRec(f, rhs, body, st) =>
        ELetRec(f, rhs.subst(from, to), body.subst(from, to), st)
      case ECond(e1, e2, e3, s) =>
        ECond(e1.subst(from, to), e2.subst(from, to), e3.subst(from, to), s)
      case EBinOp(op, e1, e2, s) => EBinOp(op, e1.subst(from, to), e2.subst(from, to), s)
      case EUnaryOp(op, e, s) => EUnaryOp(op, e.subst(from, to), s)
      case EAlloc(e, s) => EAlloc(e.subst(from, to), s)
      case EDeref(e, s) => EDeref(e.subst(from, to), s)
      case EAssign(e1, e2, s) => EAssign(e1.subst(from, to), e2.subst(from, to), s)
      case EAscribe(e, asTy) => EAscribe(e.subst(from, to), asTy)

given Conversion[Stage, Option[Stage]] = Some(_)

import Type.*
import Expr.*

def ENum1(i: Int): Expr = ENum(i)
def ENum2(i: Int): Expr = ELift2(ENum(i))
def EBool1(b: Boolean): Expr = EBool(b)
def EBool2(b: Boolean): Expr = ELift2(EBool(b))
def EApp1(e1: Expr, e2: Expr): Expr = EApp(e1, e2, Some(Sta))
def EApp2(e1: Expr, e2: Expr): Expr = EApp(e1, e2, Some(Dyn))
def ECond1(e1: Expr, e2: Expr, e3: Expr): Expr = ECond(e1, e2, e3, Some(Sta))
def ECond2(e1: Expr, e2: Expr, e3: Expr): Expr = ECond(e1, e2, e3, Some(Dyn))
def EBinOp1(op: String, e1: Expr, e2: Expr): Expr = EBinOp(op, e1, e2, Some(Sta))
def EBinOp2(op: String, e1: Expr, e2: Expr): Expr = EBinOp(op, e1, e2, Some(Dyn))
def EUnaryOp1(op: String, e: Expr): Expr = EUnaryOp(op, e, Some(Sta))
def EUnaryOp2(op: String, e: Expr): Expr = EUnaryOp(op, e, Some(Dyn))
def EAlloc1(e: Expr): Expr = EAlloc(e, Some(Sta))
def EAlloc2(e: Expr): Expr = EAlloc(e, Some(Dyn))
def EDeref1(e: Expr): Expr = EDeref(e, Some(Sta))
def EDeref2(e: Expr): Expr = EDeref(e, Some(Dyn))
def EAssign1(e1: Expr, e2: Expr): Expr = EAssign(e1, e2, Some(Sta))
def EAssign2(e1: Expr, e2: Expr): Expr = EAssign(e1, e2, Some(Dyn))

// Note: they lift term to stage 1/2, but lift itself can only be at stage 1
def ELift1(e: Expr): Expr = ELift(e, Sta)
def ELift2(e: Expr): Expr = ELift(e, Dyn)
