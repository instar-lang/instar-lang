// Section 2: Revisiting the WadlerFest stateful evaluator.
// A direct-style staged evaluator using mutable state for let-insertion.

package instar.experiment.wadlerfest

import instar.Counter.*
import instar.experiment.*

import Stage.*
import Expr.*
import Value.*

var stBlock: List[(String, Expr)] = List()

def reify(f: => Value): Expr =
  val prev = stBlock
  stBlock = List()
  val VCode(last) = f
  val e = stBlock.foldRight(last):
    case ((x, s), acc) => ELet(x, s, acc)
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
    case VClo(x, body, ρf) =>
      val y = fresh()
      val t = reify:
        eval(body, ρf + (x -> VCode(EVar(y))))
      reflect(ELam(y, t))

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

def eval(e: Expr, ρ: Env): Value =
  e match
    case EUnit => VUnit
    case ENum(i) => VNum(i)
    case EBool(b) => VBool(b)
    case EVar(x) => ρ(x)
    case ELam(x, e) => VClo(x, e, ρ)
    case EApp(e1, e2, Sta) =>
      val VClo(x, body, ρf) = eval(e1, ρ)
      val v2 = eval(e2, ρ)
      eval(body, ρf + (x -> v2))
    case EApp(e1, e2, Dyn) =>
      val VCode(x1) = eval(e1, ρ)
      val VCode(x2) = eval(e2, ρ)
      reflect(EApp1(x1, x2))
    case ELift(e) =>
      lift(eval(e, ρ))
    case ERun(e) =>
      val t = reify { eval(e, ρ) }
      eval(t, Map())
    case ELet(x, rhs, e) =>
      val v = eval(rhs, ρ)
      eval(e, ρ + (x -> v))
    case ECond(e1, e2, e3, Sta) =>
      val VBool(b) = eval(e1, ρ)
      if b then eval(e2, ρ) else eval(e3, ρ)
    case ECond(e1, e2, e3, Dyn) =>
      val VCode(x1) = eval(e1, ρ)
      val x2 = reify { eval(e2, ρ) }
      val x3 = reify { eval(e3, ρ) }
      reflect(ECond1(x1, x2, x3))
    case EBinOp(op, e1, e2, Sta) =>
      val v1 = eval(e1, ρ)
      val v2 = eval(e2, ρ)
      evalPrim(op, v1, v2)
    case EBinOp(op, e1, e2, Dyn) =>
      val VCode(x1) = eval(e1, ρ)
      val VCode(x2) = eval(e2, ρ)
      reflect(EBinOp1(op, x1, x2))
    case EUnaryOp(op, e, Sta) =>
      val v = eval(e, ρ)
      evalPrimUnary(op, v)
    case EUnaryOp(op, e, Dyn) =>
      val VCode(x) = eval(e, ρ)
      reflect(EUnaryOp1(op, x))

def eval(e: Expr): Value =
  clear
  stBlock = List()
  val v = eval(e, Map())
  if stBlock.isEmpty then v
  else
    val VCode(r) = v
    VCode(stBlock.foldRight(r) { case ((x, s), acc) => ELet(x, s, acc) })
