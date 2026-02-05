package spmp.core.absmach

import spmp.Counter.*

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

enum Cont:
  case KHalt
  case KAppL(e: Expr, st: Stage, ρ: Env, k: Cont)
  case KAppR(v: Value, st: Stage, k: Cont)
  case KLift(k: Cont)
  case KBinOpL(op: String, e: Expr, st: Stage, ρ: Env, k: Cont)
  case KBinOpR(op: String, v: Value, st: Stage, k: Cont)
  case KCond(e2: Expr, e3: Expr, st: Stage, ρ: Env, k: Cont)

enum MCont:
  case MHalt
  case MLetc(x: String, rhs: Expr, γ: MCont)
  case MLamc(x: String, k: Cont, γ: MCont)
  case MRun(k: Cont, γ: MCont)
  case MCondL(v1: Value, e3: Expr, ρ: Env, k: Cont, γ: MCont)
  case MCondR(v1: Value, v2: Value, k: Cont, γ: MCont)

enum State:
  case EState(e : Expr, ρ: Env, k: Cont, γ: MCont)
  case VState(v: Value, k: Cont, γ: MCont)

import Stage.*
import Expr.*
import Value.*
import Cont.*
import MCont.*
import State.*

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

def reflect(e: Expr, k: Cont, γ: MCont): VState =
  val x = fresh()
  VState(VCode(EVar(x)), k, MLetc(x, e, γ))

def step(s: State): State =
  s match
    // value inclusion
    case EState(EUnit, _, k, γ) => VState(VUnit, k, γ)
    case EState(ENum(i), _, k, γ) => VState(VNum(i), k, γ)
    case EState(EBool(b), _, k, γ) => VState(VBool(b), k, γ)
    case EState(ELam(x, body), ρ, k, γ) => VState(VClo(x, body, ρ), k, γ)
    // free variable
    case EState(EVar(x), ρ, k, γ) => VState(ρ(x), k, γ)
    // application
    case EState(EApp(e1, e2, st), ρ, k, γ) =>
      EState(e1, ρ, KAppL(e2, st, ρ, k), γ)
    case VState(v, KAppL(e2, st, ρ, k), γ) =>
      EState(e2, ρ, KAppR(v, st, k), γ)
    case VState(v, KAppR(VClo(x, body, ρ), Sta, k), γ) =>
      EState(body, ρ + (x -> v), k, γ)
    case VState(VCode(e2), KAppR(VCode(e1), Dyn, k), γ) =>
      reflect(EApp1(e1, e2), k, γ)
    // lift
    case EState(ELift(e), ρ, k, γ) =>
      EState(e, ρ, KLift(k), γ)
    case VState(VUnit, KLift(k), γ) =>
      VState(VCode(EUnit), k, γ)
    case VState(VNum(i), KLift(k), γ) =>
      VState(VCode(ENum(i)), k, γ)
    case VState(VBool(b), KLift(k), γ) =>
      VState(VCode(EBool(b)), k, γ)
    // lift lambda
    case VState(VClo(x, body, ρ), KLift(k), γ) =>
      val y = fresh()
      EState(body, ρ + (x -> VCode(EVar(y))), KHalt, MLamc(y, k, γ))
    case VState(VCode(body), KHalt, MLamc(x, k, γ)) =>
      reflect(ELam(x, body), k, γ)
    // run
    case EState(ERun(e), ρ, k, γ) =>
      EState(e, ρ, KHalt, MRun(k, γ))
    case VState(VCode(e), KHalt, MRun(k, γ)) =>
      EState(e, Map(), k, γ)
    // let binding
    case EState(ELet(x, rhs, body), ρ, k, γ) =>
      EState(EApp(ELam(x, body), rhs, Sta), ρ, k, γ)
    // if condition
    case EState(ECond(e1, e2, e3, st), ρ, k, γ) =>
      EState(e1, ρ, KCond(e2, e3, st, ρ, k), γ)
    case VState(VBool(b), KCond(e2, e3, Sta, ρ, k), γ) =>
      if b then EState(e2, ρ, k, γ) else EState(e3, ρ, k, γ)
    case VState(v1, KCond(e2, e3, Dyn, ρ, k), γ) =>
      EState(e2, ρ, KHalt, MCondL(v1, e3, ρ, k, γ))
    case VState(v2, KHalt, MCondL(v1, e3, ρ, k, γ)) =>
      EState(e3, ρ, KHalt, MCondR(v1, v2, k, γ))
    case VState(VCode(e3), KHalt, MCondR(VCode(e1), VCode(e2), k, γ)) =>
      reflect(ECond1(e1, e2, e3), k, γ)
    // binary operation
    case EState(EBinOp(op, e1, e2, st), ρ, k, γ) =>
      EState(e1, ρ, KBinOpL(op, e2, st, ρ, k), γ)
    case VState(v, KBinOpL(op, e2, st, ρ, k), γ) =>
      EState(e2, ρ, KBinOpR(op, v, st, k), γ)
    case VState(v2, KBinOpR(op, v1, Sta, k), γ) =>
      VState(evalPrim(op, v1, v2), k, γ)
    case VState(VCode(e2), KBinOpR(op, VCode(e1), Dyn, k), γ) =>
      reflect(EBinOp1(op, e1, e2), k, γ)
    // reify
    case VState(VCode(body), KHalt, MLetc(x, rhs, γ)) =>
      VState(VCode(ELet(x, rhs, body)), KHalt, γ)
    case _ => ???

def isDone(s: State): Boolean =
  s match
    case VState(_, KHalt, MHalt) => true
    case _ => false

def stepn(s: State): State =
  if isDone(s) then s
  else stepn(step(s))

def eval(e: Expr): Value =
  reset
  stepn(EState(e, Map(), KHalt, MHalt)) match
    case VState(v, KHalt, MHalt) => v
    case _ => ???
