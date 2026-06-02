// Section 3.2: 2-CPS definitional interpreter — fully tail-call, evaluation-strategy independent.
// Introduces a meta-continuation to complete let-expression assembly in tail position.

package instar.twocps

import instar.counter.*
import instar.*

import Stage.*
import Expr.*
import Value.*

type Cont = (Value, MCont) => Value
type MCont = Value => Value

def reflect(e: Expr, k: Cont, γ: MCont): Value =
  val x = fresh()
  k(VCode(EVar(x)), { case VCode(t) =>
    γ(VCode(ELet(x, e, t)))
  })

def reify(e: Expr, ρ: Env, γ: MCont): Value =
  eval(e, ρ, (x, γ1) => γ1(x), γ)

def lift(k: Cont)(v: Value, γ: MCont): Value =
  v match
    case VNum(i) => reflect(ENum(i), k, γ)
    case VBool(b) => reflect(EBool(b), k, γ)
    case VClo(x, body, ρf) =>
      val y = fresh()
      reify(body, ρf + (x -> VCode(EVar(y))), { case VCode(t) =>
        reflect(ELam(y, t), k, γ)
      })

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
    case _ => throw new RuntimeException("Unexpected operation")

def eval(e: Expr, ρ: Env, k: Cont, γ: MCont): Value =
  e match
    case ENum(i) => k(VNum(i), γ)
    case EBool(b) => k(VBool(b), γ)
    case EVar(x) => k(ρ(x), γ)
    case ELam(x, body) => k(VClo(x, body, ρ), γ)
    case EApp(e1, e2, Sta) =>
      eval(e1, ρ, { case (VClo(x, body, ρf), γ1) =>
        eval(e2, ρ, (v2, γ2) =>
          eval(body, ρf + (x -> v2), k, γ2), γ1)
      }, γ)
    case EApp(e1, e2, Dyn) =>
      eval(e1, ρ, { case (VCode(x1), γ1) =>
        eval(e2, ρ, { case (VCode(x2), γ2) =>
          reflect(EApp1(x1, x2), k, γ2)
        }, γ1)
      }, γ)
    case ELift(e) =>
      eval(e, ρ, lift(k), γ)
    case ERun(e) =>
      reify(e, ρ, { case VCode(t) =>
        eval(t, Map(), k, γ)
      })
    case ELet(x, rhs, e) =>
      eval(rhs, ρ, (v, γ1) => eval(e, ρ + (x -> v), k, γ1), γ)
    case ECond(e1, e2, e3, Sta) =>
      eval(e1, ρ, { case (VBool(b), γ1) =>
        if b then eval(e2, ρ, k, γ1)
        else eval(e3, ρ, k, γ1)
      }, γ)
    case ECond(e1, e2, e3, Dyn) =>
      eval(e1, ρ, { case (VCode(x1), γ1) =>
        reify(e2, ρ, { case VCode(x2) =>
          reify(e3, ρ, { case VCode(x3) =>
            reflect(ECond1(x1, x2, x3), k, γ1)
          })
        })
      }, γ)
    case EBinOp(op, e1, e2, Sta) =>
      eval(e1, ρ, { case (v1, γ1) =>
        eval(e2, ρ, { case (v2, γ2) =>
          k(evalPrim(op, v1, v2), γ2)
        }, γ1)
      }, γ)
    case EBinOp(op, e1, e2, Dyn) =>
      eval(e1, ρ, { case (VCode(x1), γ1) =>
        eval(e2, ρ, { case (VCode(x2), γ2) =>
          reflect(EBinOp1(op, x1, x2), k, γ2)
        }, γ1)
      }, γ)

def eval(e: Expr): Value =
  clear
  eval(e, Map(), (x, γ) => γ(x), x => x)
