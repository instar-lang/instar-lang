package spmp.core.imp.cps1

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

def reify(e: Expr, ρ: Env, ς: StEnv): Expr =
  // evaluate term under the identity continuation, and the term should return a code value
  val VCode(t) = eval(e, ρ, ς, v => v)
  t

def reflect(e: Expr, k: Value => Value): Value =
  val z = fresh()
  // How should we form a let-binding with let z = lam in ... here, as we don't know the body of let!
  val VCode(t) = k(VCode(EVar(z)))
  VCode(ELet(z, e, t))

def lift(v: Value, k: Value => Value): Value =
  v match
    case VUnit => reflect(EUnit, k)
    case VNum(i) => reflect(ENum(i), k)
    case VBool(b) => reflect(EBool(b), k)
    case VClo(x, argTy, body, retTy, ρ, ςf) =>
      val y = fresh()
      val t = reify(body, ρ + (x -> VCode(EVar(y))), ςf)
      reflect(ELam(y, argTy.erase, t, retTy.erase), k)

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

def eval(e: Expr, ρ: Env, ς: StEnv, k: Value => Value): Value =
  e match
    case EUnit =>
      k(VUnit)
    case ENum(i) =>
      k(VNum(i))
    case EBool(b) =>
      k(VBool(b))
    case EVar(x) =>
      k(ρ(x))
    case ESLam(x, body) =>
      k(VSClo(x, body, ρ, ς))
    case ESApp(e, st) =>
      eval(e, ρ, ς, { case VSClo(x, body, ρf, ςf) =>
        eval(body, ρf, ςf + (x -> evalStVar(st, ς)), k)
      })
    case ELam(x, argTy, e, retTy) =>
      k(VClo(x, argTy, e, retTy, ρ, ς))
    case EApp(e1, e2, s) if evalStVar(s, ς) == Sta =>
      eval(e1, ρ, ς, { case VClo(x, _, body, _, ρf, ςf) =>
        eval(e2, ρ, ς, v2 =>
          eval(body, ρf + (x -> v2), ςf, k))
      })
    case EApp(e1, e2, s) if evalStVar(s, ς) == Dyn =>
      eval(e1, ρ, ς, { case VCode(x1) =>
        eval(e2, ρ, ς, { case VCode(x2) =>
          reflect(EApp1(x1, x2), k)
        })
      })
    case ELift(e, to) if evalStVar(to, ς) == Sta =>
      eval(e, ρ, ς, k)
    case ELift(e, to) if evalStVar(to, ς) == Dyn =>
      eval(e, ρ, ς, v => lift(v, k))
    case ERun(e) =>
      eval(e, ρ, ς, { case VCode(t) => eval(t, ρ, ς, k) })
    case ELet(x, rhs, e) =>
      eval(rhs, ρ, ς, v =>
        eval(e, ρ + (x -> v), ς, k))
    case ECond(e1, e2, e3, s) if evalStVar(s, ς) == Sta =>
      eval(e1, ρ, ς, { case VBool(b) =>
        if b then eval(e2, ρ, ς, k)
        else eval(e3, ρ, ς, k) })
    case ECond(e1, e2, e3, s) if evalStVar(s, ς) == Dyn =>
      eval(e1, ρ, ς, { case VCode(x1) =>
        val x2 = reify(e2, ρ, ς)
        val x3 = reify(e3, ρ, ς)
        reflect(ECond1(x1, x2, x3), k)
      })
    case EBinOp(op, e1, e2, s) if evalStVar(s, ς) == Sta =>
      eval(e1, ρ, ς, v1 =>
        eval(e2, ρ, ς, v2 =>
          evalPrim(op, v1, v2)))
    case EBinOp(op, e1, e2, s) if evalStVar(s, ς) == Dyn =>
      eval(e1, ρ, ς, { case VCode(x1) =>
        eval(e2, ρ, ς, { case VCode(x2) =>
          reflect(EBinOp1(op, x1, x2), k)
        })
      })
    case EUnaryOp(op, e, s) if evalStVar(s, ς) == Sta =>
      eval(e, ρ, ς, v => k(evalPrimUnary(op, v)))
    case EUnaryOp(op, e, s) if evalStVar(s, ς) == Dyn =>
      eval(e, ρ, ς, { case VCode(x) =>
        reflect(EUnaryOp1(op, x), k)
      })

def eval(e: Expr): Ans =
  reset
  eval(e, Map(), Map(), x => x)