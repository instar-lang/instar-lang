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
  // Experimental:
  case ELoc(l: Loc)
  // Extend the language to allow programmers to inspect code values
  case EIsApp(e: Expr)
  case ECBNApp(e1: Expr, e2: Expr)

val Sta = Stage.SNum(1)
val Dyn = Stage.SNum(2)

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
