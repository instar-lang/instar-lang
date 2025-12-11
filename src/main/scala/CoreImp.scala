package spmp.core.imp

// Note: this version uses global mutable states to manage scope and inserted let-bindings,
// pretty much close to the POPL 18 paper's big-step evaluator.
// This version is mainly for easier comparison with the 2CPS version (Core.scala).

import spmp.Counter.*

enum Stage:
  case SNum(n: Int)
  case SVar(x: String)

enum Type:
  case TUnit, TInt, TBool
  case TFun(t1: Type, t2: Type)
  case TForallSt(s: String, t: Type)
  case TAt(t: Type, s: Stage)
  case TCode(t: Type)

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
  case EApp(e1: Expr, e2: Expr, st: Stage)
  case ELift(t: Expr, to: Stage)
  case ERun(t: Expr)
  case ELet(x: String, rhs: Expr, body: Expr)
  case ECond(e1: Expr, e2: Expr, e3: Expr, st: Stage)
  case EBinOp(op: String, e1: Expr, e2: Expr, st: Stage)
  case EUnaryOp(op: String, e: Expr, st: Stage)
  case EAscribe(e: Expr, asTy: Type)

val Sta = Stage.SNum(0)
val Dyn = Stage.SNum(1)

def EApp1(e1: Expr, e2: Expr): Expr = EApp(e1, e2, Sta)
def EApp2(e1: Expr, e2: Expr): Expr = EApp(e1, e2, Dyn)
def ECond1(e1: Expr, e2: Expr, e3: Expr): Expr = ECond(e1, e2, e3, Sta)
def ECond2(e1: Expr, e2: Expr, e3: Expr): Expr = ECond(e1, e2, e3, Dyn)
def EBinOp1(op: String, e1: Expr, e2: Expr): Expr = EBinOp(op, e1, e2, Sta)
def EBinOp2(op: String, e1: Expr, e2: Expr): Expr = EBinOp(op, e1, e2, Dyn)
def EUnaryOp1(op: String, e: Expr): Expr = EUnaryOp(op, e, Sta)
def EUnaryOp2(op: String, e: Expr): Expr = EUnaryOp(op, e, Dyn)

// Note: they lift term to stage 1/2, but lift itself can only be at stage 1
def ELift1(e: Expr): Expr = ELift(e, Sta)
def ELift2(e: Expr): Expr = ELift(e, Dyn)

enum Value:
  case VUnit
  case VNum(i: Int)
  case VBool(b: Boolean)
  case VSClo(st: String, body: Expr, ρ: Env, ς: StEnv)
  case VClo(x: String, argTy: Option[Type], body: Expr, retTy: Option[Type], ρ: Env, ς: StEnv)
  case VCode(e: Expr) //XXX: could extend to open code value with environment?

extension (t: Option[Type])
  // Assuming well-formedness of types
  def erase: Option[Type] =
    t match
      case Some(TCode(t1)) => Some(t1)
      case _ => t

import Stage.*
import Expr.*
import Type.*
import Value.*

type Env = Map[String, Value]
type StEnv = Map[String, Stage]
type Ans = Value

type Cont = (Value, MCont) => Value
type MCont = Value => Value

var stBlock: List[(String, Expr)] = List()

def reify(f: => Value): Expr =
  val prev = stBlock
  stBlock = List()
  val VCode(last) = f
  val e = stBlock.foldRight(last) { case ((x, s), acc) => ELet(x, s, acc) }
  stBlock = prev
  e

def reflect(s: Expr): Value =
  val x = fresh()
  stBlock = stBlock :+ (x, s)
  VCode(EVar(x))

def lift(v: Value): Value =
  v match
    case VUnit => reflect(EUnit)
    case VNum(i) => reflect(ENum(i))
    case VBool(b) => reflect(EBool(b))
    case VClo(x, argTy, body, retTy, ρf, ςf) =>
      val y = fresh()
      val t = reify { eval(body, ρf + (x -> VCode(EVar(y))), ςf) }
      reflect(ELam(y, argTy.erase, t, retTy.erase))

def evalPrim(op: String, v1: Value, v2: Value): Value =
  (op, v1, v2) match
    case ("+", VNum(i1), VNum(i2)) => VNum(i1 + i2)
    case ("-", VNum(i1), VNum(i2)) => VNum(i1 - i2)
    case ("*", VNum(i1), VNum(i2)) => VNum(i1 * i2)
    case ("/", VNum(i1), VNum(i2)) => VNum(i1 / i2)
    case ("<=", VNum(i1), VNum(i2)) => VBool(i1 <= i2)
    case (">=", VNum(i1), VNum(i2)) => VBool(i1 >= i2)
    case ("<", VNum(i1), VNum(i2)) => VBool(i1 < i2)
    case (">", VNum(i1), VNum(i2)) => VBool(i1 > i2)
    case ("==", VNum(i1), VNum(i2)) => VBool(i1 == i2)
    case ("!=", VNum(i1), VNum(i2)) => VBool(i1 != i2)

def evalPrimUnary(op: String, v: Value): Value =
  (op, v) match
    case ("-", VNum(i)) => VNum(-i)

def evalStVar(s: Stage, ς: StEnv): Stage =
  s match
    case SVar(st) => ς(st)
    case _ => s

def eval(e: Expr, ρ: Env, ς: StEnv): Value =
  e match
    case EUnit =>
      VUnit
    case ENum(i) =>
      VNum(i)
    case EBool(b) =>
      VBool(b)
    case EVar(x) =>
      ρ(x)
    case ESLam(x, body) =>
      VSClo(x, body, ρ, ς)
    case ESApp(e, st) =>
      val VSClo(x, body, ρf, ςf) = eval(e, ρ, ς)
      eval(body, ρf, ςf + (x -> evalStVar(st, ς)))
    case ELam(x, argTy, e, retTy) =>
      VClo(x, argTy, e, retTy, ρ, ς)
    case EApp(e1, e2, s) if evalStVar(s, ς) == Sta =>
      val VClo(x, _, body, _, ρf, ςf) = eval(e1, ρ, ς)
      val v2 = eval(e2, ρ, ς)
      eval(body, ρf + (x -> v2), ςf)
    case EApp(e1, e2, s) if evalStVar(s, ς) == Dyn =>
      val VCode(x1) = eval(e1, ρ, ς)
      val VCode(x2) = eval(e2, ρ, ς)
      reflect(EApp1(x1, x2))
    case ELift(e, to) if evalStVar(to, ς) == Sta =>
      eval(e, ρ, ς)
    case ELift(e, to) if evalStVar(to, ς) == Dyn =>
      lift(eval(e, ρ, ς))
    case ERun(e) =>
      val VCode(t) = eval(e, ρ, ς)
      eval(t, ρ, ς)
    case ELet(x, rhs, e) =>
      val v = eval(rhs, ρ, ς)
      eval(e, ρ + (x -> v), ς)
    case ECond(e1, e2, e3, s) if evalStVar(s, ς) == Sta =>
      val VBool(b) = eval(e1, ρ, ς)
      if b then eval(e2, ρ, ς)
      else eval(e3, ρ, ς)
    case ECond(e1, e2, e3, s) if evalStVar(s, ς) == Dyn =>
      val VCode(x1) = eval(e1, ρ, ς)
      val x2 = reify { eval(e2, ρ, ς) }
      val x3 = reify { eval(e3, ρ, ς) }
      reflect(ECond1(x1, x2, x3))
    case EBinOp(op, e1, e2, s) if evalStVar(s, ς) == Sta =>
      val v1 = eval(e1, ρ, ς)
      val v2 = eval(e2, ρ, ς)
      evalPrim(op, v1, v2)
    case EBinOp(op, e1, e2, s) if evalStVar(s, ς) == Dyn =>
      val VCode(x1) = eval(e1, ρ, ς)
      val VCode(x2) = eval(e2, ρ, ς)
      reflect(EBinOp1(op, x1, x2))
    case EUnaryOp(op, e, s) if evalStVar(s, ς) == Sta =>
      val v = eval(e, ρ, ς)
      evalPrimUnary(op, v)
    case EUnaryOp(op, e, s) if evalStVar(s, ς) == Dyn =>
      val VCode(x) = eval(e, ρ, ς)
      reflect(EUnaryOp1(op, x))
    case EAscribe(e, _) => eval(e, ρ, ς)

def eval(e: Expr): Ans =
  reset
  stBlock = List()
  val v = eval(e, Map(), Map())
  if stBlock.isEmpty then v
  else
    val VCode(r) = v
    VCode(stBlock.foldRight(r) { case ((x, s), acc) => ELet(x, s, acc) })