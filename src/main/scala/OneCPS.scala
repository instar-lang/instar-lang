// Section 3.1: 1-CPS transformation — eliminating mutable state with a single continuation.
// Reifies ANF let-insertion via explicit delimited continuations.

package instar.onecps

import instar.Counter.*
import instar.*

import Stage.*
import Expr.*
import Value.*

def reify(e: Expr, ρ: Env): Expr =
  val VCode(t) = eval(e, ρ, v => v)
  t

def reflect(e: Expr, k: Value => Value): Value =
  val z = fresh()
  val VCode(t) = k(VCode(EVar(z)))
  VCode(ELet(z, e, t))

def lift(v: Value, k: Value => Value): Value =
  v match
    case VUnit => reflect(EUnit, k)
    case VNum(i) => reflect(ENum(i), k)
    case VBool(b) => reflect(EBool(b), k)
    case VClo(x, body, ρf) =>
      val y = fresh()
      val t = reify(body, ρf + (x -> VCode(EVar(y))))
      reflect(ELam(y, t), k)

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

def eval(e: Expr, ρ: Env, k: Value => Value): Value =
  e match
    case EUnit => k(VUnit)
    case ENum(i) => k(VNum(i))
    case EBool(b) => k(VBool(b))
    case EVar(x) => k(ρ(x))
    case ELam(x, body) => k(VClo(x, body, ρ))
    case EApp(e1, e2, Sta) =>
      eval(e1, ρ, { case VClo(x, body, ρf) =>
        eval(e2, ρ, v2 => eval(body, ρf + (x -> v2), k))
      })
    case EApp(e1, e2, Dyn) =>
      eval(e1, ρ, { case VCode(x1) =>
        eval(e2, ρ, { case VCode(x2) =>
          reflect(EApp1(x1, x2), k)
        })
      })
    case ELift(e) =>
      eval(e, ρ, v => lift(v, k))
    case ERun(e) =>
      val t = reify(e, ρ)
      eval(t, Map(), k)
    case ELet(x, rhs, e) =>
      eval(rhs, ρ, v => eval(e, ρ + (x -> v), k))
    case ECond(e1, e2, e3, Sta) =>
      eval(e1, ρ, { case VBool(b) =>
        if b then eval(e2, ρ, k) else eval(e3, ρ, k)
      })
    case ECond(e1, e2, e3, Dyn) =>
      eval(e1, ρ, { case VCode(x1) =>
        val x2 = reify(e2, ρ)
        val x3 = reify(e3, ρ)
        reflect(ECond1(x1, x2, x3), k)
      })
    case EBinOp(op, e1, e2, Sta) =>
      eval(e1, ρ, v1 => eval(e2, ρ, v2 => k(evalPrim(op, v1, v2))))
    case EBinOp(op, e1, e2, Dyn) =>
      eval(e1, ρ, { case VCode(x1) =>
        eval(e2, ρ, { case VCode(x2) =>
          reflect(EBinOp1(op, x1, x2), k)
        })
      })
    case EUnaryOp(op, e, Sta) =>
      eval(e, ρ, v => k(evalPrimUnary(op, v)))
    case EUnaryOp(op, e, Dyn) =>
      eval(e, ρ, { case VCode(x) =>
        reflect(EUnaryOp1(op, x), k)
      })

def eval(e: Expr): Value =
  clear
  eval(e, Map(), x => x)
