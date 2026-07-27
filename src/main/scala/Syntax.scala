package instar.syntax

import scala.language.implicitConversions

enum Stage:
  case SNum(n: Int)
  case SVar(x: String)

enum Type:
  case TUnit, TInt, TBool
  case TFun(t1: Type, t2: Type)
  case TRef(t: Type)
  case TForallSt(s: String, t: Type)
  case TAt(t: Type, s: Stage)
  case TCode(t: Type)

type Loc = Int

enum Expr:
  var ty: Option[Type] = None
  def withType(t: Type): Expr = { ty = Some(t); this }
  case EUnit
  case ENum(i: Int)
  case EBool(b: Boolean)
  case EVar(name: String)
  case ESLam(x: String, body: Expr)
  case ESApp(e: Expr, st: Stage)
  case ELam(x: String, argTy: Option[Type], body: Expr, retTy: Option[Type])
  case EBNLam(x: String, argTy: Option[Type], body: Expr, retTy: Option[Type])
  case EApp(e1: Expr, e2: Expr, st: Option[Stage])
  case ELift(t: Expr, to: Stage)
  case ERun(t: Expr)
  case ELet(x: String, rhs: Expr, body: Expr)
  case ELetRec(f: String, rhs: Expr, body: Expr)
  case ECond(e1: Expr, e2: Expr, e3: Expr, st: Option[Stage])
  case EBinOp(op: String, e1: Expr, e2: Expr, st: Option[Stage])
  case EUnaryOp(op: String, e: Expr, st: Option[Stage])
  case EAlloc(e: Expr, st: Option[Stage])
  case EDeref(e: Expr, st: Option[Stage])
  case EAssign(e1: Expr, e2: Expr, st: Option[Stage])
  case EAscribe(e: Expr, asTy: Type)
  case EFix(f: String, e: Expr, st: Option[Stage])
  // brack/esc extension
  case EBracket(e: Expr)
  case EEscape(e: Expr)
  // Experimental:
  case ELoc(l: Loc)
  // Extend the language to allow programmers to inspect code values
  case EIsApp(e: Expr)
  case ECBNApp(e1: Expr, e2: Expr)

val Sta: Stage.SNum = Stage.SNum(1)
val Dyn: Stage.SNum = Stage.SNum(2)

extension (e: Expr)
  def isPure: Boolean =
    e match
      case EUnit | ENum(_) | EBool(_) | EVar(_) => true
      case ESLam(_, _) | ELam(_, _, _, _) | EBNLam(_, _, _, _) => true
      case EBinOp(_, _, _, _) | EUnaryOp(_, _, _) => true
      case ESApp(_, _) | EApp(_, _, _) => false
      case ELift(t, _) => false
      case EAlloc(_, _) | EDeref(_, _) | EAssign(_, _, _) => false
      case ERun(t) => t.isPure
      case ELet(_, rhs, body) => rhs.isPure && body.isPure
      case ELetRec(_, rhs, body) => rhs.isPure && body.isPure
      case ECond(e1, e2, e3, _) => e1.isPure && e2.isPure && e3.isPure
      case EAscribe(e, _) => e.isPure
      case EFix(_, e, _) => e.isPure
      case _ => false

  def freeVar: Set[String] =
    e match
      case EUnit | ENum(_) | EBool(_) => Set()
      case EVar(x) => Set(x)
      case ESLam(x, body) => body.freeVar
      case ESApp(e, _) => e.freeVar
      case ELam(x, _, body, _) => body.freeVar - x
      case EApp(e1, e2, _) => e1.freeVar ++ e2.freeVar
      case ECBNApp(e1, e2) => e1.freeVar ++ e2.freeVar
      case ELift(t, _) => t.freeVar
      case ERun(t) => t.freeVar
      case ELet(x, rhs, body) => rhs.freeVar ++ (body.freeVar - x)
      case ELetRec(f, rhs, body) => (rhs.freeVar - f) ++ (body.freeVar - f)
      case ECond(e1, e2, e3, _) => e1.freeVar ++ e2.freeVar ++ e3.freeVar
      case EBinOp(_, e1, e2, _) => e1.freeVar ++ e2.freeVar
      case EUnaryOp(_, e, _) => e.freeVar
      case EAlloc(e, _) => e.freeVar
      case EDeref(e, _) => e.freeVar
      case EAssign(e1, e2, _) => e1.freeVar ++ e2.freeVar
      case EAscribe(e, _) => e.freeVar
      case EFix(f, e, _) => e.freeVar - f

  // We only use this function to substitute the binding variable with the argument (which is always a pure, atomic expression),
  // and all variables after reflect are distinct, so we do not need to consider variable capture here.
  def subst(from: String, to: Expr): Expr =
    e match
      case EUnit | ENum(_) | EBool(_) => e
      case EVar(x) => if x == from then to else e
      case ESLam(x, body) => ESLam(x, body.subst(from, to))
      case ESApp(e, st) => ESApp(e.subst(from, to), st)
      case ELam(x, argTy, body, retTy) =>
        ELam(x, argTy, body.subst(from, to), retTy)
      case EApp(e1, e2, st) => EApp(e1.subst(from, to), e2.subst(from, to), st)
      case ELift(t, s) => ELift(t.subst(from, to), s)
      case ERun(t) => ERun(t.subst(from, to))
      case ELet(x, rhs, body) =>
        ELet(x, rhs.subst(from, to), body.subst(from, to))
      case ELetRec(f, rhs, body) =>
        ELetRec(f, rhs.subst(from, to), body.subst(from, to))
      case ECond(e1, e2, e3, s) =>
        ECond(e1.subst(from, to), e2.subst(from, to), e3.subst(from, to), s)
      case EBinOp(op, e1, e2, s) => EBinOp(op, e1.subst(from, to), e2.subst(from, to), s)
      case EUnaryOp(op, e, s) => EUnaryOp(op, e.subst(from, to), s)
      case EAlloc(e, s) => EAlloc(e.subst(from, to), s)
      case EDeref(e, s) => EDeref(e.subst(from, to), s)
      case EAssign(e1, e2, s) => EAssign(e1.subst(from, to), e2.subst(from, to), s)
      case EAscribe(e, asTy) => EAscribe(e.subst(from, to), asTy)
      case EFix(f, e, s) =>
        EFix(f, e.subst(from, to), s)

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
