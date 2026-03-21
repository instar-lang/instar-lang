package instar.experiment.delimited

import instar.Counter.*
import instar.Cont.*

enum Stage:
  case Sta, Dyn

enum Expr:
  case EUnit
  case ENum(i: Int)
  case EBool(b: Boolean)
  case EVar(name: String)
  case ELam(x: String, body: Expr)
  case EApp(e1: Expr, e2: Expr, st: Stage)
  case ELift(t: Expr)
  case ERun(t: Expr)
  case ELet(x: String, rhs: Expr, body: Expr)
  case ECond(e1: Expr, e2: Expr, e3: Expr, st: Stage)
  case EBinOp(op: String, e1: Expr, e2: Expr, st: Stage)

def EApp1(e1: Expr, e2: Expr): Expr = EApp(e1, e2, Sta)
def EApp2(e1: Expr, e2: Expr): Expr = EApp(e1, e2, Dyn)
def ECond1(e1: Expr, e2: Expr, e3: Expr): Expr = ECond(e1, e2, e3, Sta)
def ECond2(e1: Expr, e2: Expr, e3: Expr): Expr = ECond(e1, e2, e3, Dyn)
def EBinOp1(op: String, e1: Expr, e2: Expr): Expr = EBinOp(op, e1, e2, Sta)
def EBinOp2(op: String, e1: Expr, e2: Expr): Expr = EBinOp(op, e1, e2, Dyn)

enum Value:
  case VUnit
  case VNum(i: Int)
  case VBool(b: Boolean)
  case VClo(x: String, body: Expr, ρ: Env)
  case VCode(e: Expr)

type Env = Map[String, Value]

import Stage.*
import Expr.*
import Value.*

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

def reflect(e: Expr): Cont[Value, Value] =
  e match
    // Note: here we decide what needs to be let-inserted based on syntactic form.
    // We could also avoid let-inserting for λ-terms and fix as they are pure.
    case EUnit | ENum(_) | EBool(_) => pure(VCode(e))
    case _ =>
      val x = fresh()
      shift: k =>
        for case VCode(t) <- k(VCode(EVar(x)))
        yield VCode(ELet(x, e, t))

def reify(e: Expr, ρ: Env): Cont[Value, Value] =
  reset(eval(e, ρ))

def lift(v: Value): Cont[Value, Value] =
  v match
    case VUnit => reflect(EUnit)
    case VNum(i) => reflect(ENum(i))
    case VBool(b) => reflect(EBool(b))
    case VClo(x, body, ρf) =>
      val y = fresh()
      for
        case VCode(t) <- reify(body, ρf + (x -> VCode(EVar(y))))
        v2 <- reflect(ELam(y, t))
      yield v2

def eval(e: Expr, ρ: Env): Cont[Value, Value] =
  e match
    case EUnit => pure(VUnit)
    case ENum(i) => pure(VNum(i))
    case EBool(b) => pure(VBool(b))
    case EVar(x) => pure(ρ(x))
    case ELam(x, body) => pure(VClo(x, body, ρ))
    case EApp(e1, e2, Sta) =>
      for
        case VClo(x, body, ρf) <- eval(e1, ρ)
        v2 <- eval(e2, ρ)
        v3 <- eval(body, ρf + (x -> v2))
      yield v3
    case EApp(e1, e2, Dyn) =>
      for
        case VCode(x1) <- eval(e1, ρ)
        case VCode(x2) <- eval(e2, ρ)
        v3 <- reflect(EApp1(x1, x2))
      yield v3
    case ELift(e) =>
      for
        v1 <- eval(e, ρ)
        v2 <- lift(v1)
      yield v2
    case ERun(e) =>
      for
        case VCode(t) <- reify(e, ρ)
        v2 <- eval(t, Map())
      yield v2
    case ELet(x, rhs, body) =>
      for
        v1 <- eval(rhs, ρ)
        v2 <- eval(body, ρ + (x -> v1))
      yield v2
    case ECond(e1, e2, e3, Sta) =>
      for
        case VBool(b) <- eval(e1, ρ)
        v <- if b then eval(e2, ρ) else eval(e3, ρ)
      yield v
    case ECond(e1, e2, e3, Dyn) =>
      for
        case VCode(x1) <- eval(e1, ρ)
        case VCode(x2) <- reify(e2, ρ)
        case VCode(x3) <- reify(e3, ρ)
        v3 <- reflect(ECond1(x1, x2, x3))
      yield v3
    case EBinOp(op, e1, e2, Sta) =>
      for
        v1 <- eval(e1, ρ)
        v2 <- eval(e2, ρ)
      yield evalPrim(op, v1, v2)
    case EBinOp(op, e1, e2, Dyn) =>
      for
        case VCode(x1) <- eval(e1, ρ)
        case VCode(x2) <- eval(e2, ρ)
        v3 <- reflect(EBinOp1(op, x1, x2))
      yield v3

def eval(e: Expr): Value =
  clear
  runCont(eval(e, Map()))
