// Section 4: CEKM abstract machine — defunctionalized 2-CPS interpreter.
// Explicitly represents continuations and meta-continuations as stacks.

package instar.experiment.cekm

import instar.Counter.*
import instar.experiment.*

import Stage.*
import Expr.*
import Value.*

enum Cont:
  case KHalt
  case KAppL(e: Expr, st: Stage, ρ: Env, k: Cont)
  case KAppR(v: Value, st: Stage, k: Cont)
  case KLift(k: Cont)
  case KBinOpL(op: String, e: Expr, st: Stage, ρ: Env, k: Cont)
  case KBinOpR(op: String, v: Value, st: Stage, k: Cont)
  case KCond(e2: Expr, e3: Expr, st: Stage, ρ: Env, k: Cont)
  case KLetc(x: String, rhs: Expr)
  case KLamc(x: String, k: Cont)
  case KRun(k: Cont)
  case KCondL(v1: Value, e3: Expr, ρ: Env, k: Cont)
  case KCondR(v1: Value, v2: Value, k: Cont)

enum MCont:
  case MHalt
  case MCons(k: Cont, γ: MCont)

enum State:
  case EState(e: Expr, ρ: Env, k: Cont, γ: MCont)
  case VState(v: Value, k: Cont, γ: MCont)
  case AState(v: Value, γ: MCont)

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
  VState(VCode(EVar(x)), k, MCons(KLetc(x, e), γ))

def continue(s: State): State =
  s match
    case VState(v, KAppL(e2, st, ρ, k), γ) =>
      EState(e2, ρ, KAppR(v, st, k), γ)
    case VState(v, KAppR(VClo(x, body, ρ), Sta, k), γ) =>
      EState(body, ρ + (x -> v), k, γ)
    case VState(VCode(e2), KAppR(VCode(e1), Dyn, k), γ) =>
      reflect(EApp1(e1, e2), k, γ)
    case VState(VUnit, KLift(k), γ) =>
      VState(VCode(EUnit), k, γ)
    case VState(VNum(i), KLift(k), γ) =>
      VState(VCode(ENum(i)), k, γ)
    case VState(VBool(b), KLift(k), γ) =>
      VState(VCode(EBool(b)), k, γ)
    case VState(VClo(x, body, ρ), KLift(k), γ) =>
      val y = fresh()
      EState(body, ρ + (x -> VCode(EVar(y))), KHalt, MCons(KLamc(y, k), γ))
    case VState(VCode(body), KLamc(x, k), γ) =>
      reflect(ELam(x, body), k, γ)
    case VState(VCode(e), KRun(k), γ) =>
      EState(e, Map(), k, γ)
    case VState(VBool(b), KCond(e2, e3, Sta, ρ, k), γ) =>
      if b then EState(e2, ρ, k, γ) else EState(e3, ρ, k, γ)
    case VState(v1, KCond(e2, e3, Dyn, ρ, k), γ) =>
      EState(e2, ρ, KHalt, MCons(KCondL(v1, e3, ρ, k), γ))
    case VState(v2, KCondL(v1, e3, ρ, k), γ) =>
      EState(e3, ρ, KHalt, MCons(KCondR(v1, v2, k), γ))
    case VState(VCode(e3), KCondR(VCode(e1), VCode(e2), k), γ) =>
      reflect(ECond1(e1, e2, e3), k, γ)
    case VState(v, KBinOpL(op, e2, st, ρ, k), γ) =>
      EState(e2, ρ, KBinOpR(op, v, st, k), γ)
    case VState(v2, KBinOpR(op, v1, Sta, k), γ) =>
      VState(evalPrim(op, v1, v2), k, γ)
    case VState(VCode(e2), KBinOpR(op, VCode(e1), Dyn, k), γ) =>
      reflect(EBinOp1(op, e1, e2), k, γ)
    case VState(VCode(body), KLetc(x, rhs), γ) =>
      AState(VCode(ELet(x, rhs, body)), γ)
    case VState(v, KHalt, γ) => AState(v, γ)
    case _ => mcontinue(s)

def mcontinue(s: State): State =
  s match
    case AState(v, MCons(k, γ)) => VState(v, k, γ)

def step(s: State): State =
  s match
    case EState(EUnit, _, k, γ) => VState(VUnit, k, γ)
    case EState(ENum(i), _, k, γ) => VState(VNum(i), k, γ)
    case EState(EBool(b), _, k, γ) => VState(VBool(b), k, γ)
    case EState(ELam(x, body), ρ, k, γ) => VState(VClo(x, body, ρ), k, γ)
    case EState(EVar(x), ρ, k, γ) => VState(ρ(x), k, γ)
    case EState(EApp(e1, e2, st), ρ, k, γ) =>
      EState(e1, ρ, KAppL(e2, st, ρ, k), γ)
    case EState(ELift(e), ρ, k, γ) =>
      EState(e, ρ, KLift(k), γ)
    case EState(ERun(e), ρ, k, γ) =>
      EState(e, ρ, KHalt, MCons(KRun(k), γ))
    case EState(ELet(x, rhs, body), ρ, k, γ) =>
      EState(EApp(ELam(x, body), rhs, Sta), ρ, k, γ)
    case EState(ECond(e1, e2, e3, st), ρ, k, γ) =>
      EState(e1, ρ, KCond(e2, e3, st, ρ, k), γ)
    case EState(EBinOp(op, e1, e2, st), ρ, k, γ) =>
      EState(e1, ρ, KBinOpL(op, e2, st, ρ, k), γ)
    case _ => continue(s)

def isDone(s: State): Boolean =
  s match
    case AState(_, MHalt) => true
    case _ => false

def stepn(s: State): State =
  if isDone(s) then s
  else stepn(step(s))

def eval(e: Expr): Value =
  clear
  stepn(EState(e, Map(), KHalt, MHalt)) match
    case AState(v, MHalt) => v
    case _ => throw new RuntimeException("Expect a final answer")
