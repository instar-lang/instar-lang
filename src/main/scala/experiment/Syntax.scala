// Shared core two-stage language syntax (Figure 2).
// Used by all definitional interpreters and the CEKM machine.

package instar.experiment

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
  case EUnaryOp(op: String, e: Expr, st: Stage)

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

def ENum1(i: Int): Expr = ENum(i)
def ENum2(i: Int): Expr = ELift(ENum(i))
def EBool1(b: Boolean): Expr = EBool(b)
def EBool2(b: Boolean): Expr = ELift(EBool(b))
def EApp1(e1: Expr, e2: Expr): Expr = EApp(e1, e2, Sta)
def EApp2(e1: Expr, e2: Expr): Expr = EApp(e1, e2, Dyn)
def ECond1(e1: Expr, e2: Expr, e3: Expr): Expr = ECond(e1, e2, e3, Sta)
def ECond2(e1: Expr, e2: Expr, e3: Expr): Expr = ECond(e1, e2, e3, Dyn)
def EBinOp1(op: String, e1: Expr, e2: Expr): Expr = EBinOp(op, e1, e2, Sta)
def EBinOp2(op: String, e1: Expr, e2: Expr): Expr = EBinOp(op, e1, e2, Dyn)
def EUnaryOp1(op: String, e: Expr): Expr = EUnaryOp(op, e, Sta)
def EUnaryOp2(op: String, e: Expr): Expr = EUnaryOp(op, e, Dyn)

def show(e: Expr): String = pprint(e, 0)

private def pprint(e: Expr, d: Int): String =
  val I = "  " * d
  e match
    case EUnit => "()"
    case ENum(i) => i.toString
    case EBool(b) => b.toString
    case EVar(x) => x
    case ELam(x, b) => s"λ$x.\n${pprint(b, d + 1)}"
    case EApp(e1, e2, Sta) => s"(${show(e1)} ${show(e2)})"
    case EApp(e1, e2, Dyn) => s"(${show(e1)} @² ${show(e2)})"
    case ELift(t) => s"lift(${show(t)})"
    case ERun(t) => s"run(${show(t)})"
    case ELet(x, r, b) =>
      val bodyStr = pprint(b, d)
      val body = if bodyStr.contains('\n') then bodyStr else s"$I$bodyStr"
      s"${I}let $x = ${pprint(r, d)} in\n$body"
    case ECond(e1, e2, e3, Sta) =>
      s"if ${show(e1)}\n${I}then\n${pprint(e2, d + 1)}\n${I}else\n${pprint(e3, d + 1)}"
    case ECond(e1, e2, e3, Dyn) =>
      s"if² ${show(e1)}\n${I}then\n${pprint(e2, d + 1)}\n${I}else\n${pprint(e3, d + 1)}"
    case EBinOp(op, e1, e2, Sta) => s"(${pprint(e1, 0)} $op ${pprint(e2, 0)})"
    case EBinOp(op, e1, e2, Dyn) => s"(${pprint(e1, 0)} $op² ${pprint(e2, 0)})"
    case EUnaryOp(op, e, Sta) => s"($op ${pprint(e, 0)})"
    case EUnaryOp(op, e, Dyn) => s"($op² ${pprint(e, 0)})"

def show(v: Value): String = v match
  case VCode(e) => s"⟨code:\n${pprint(e, 1)}⟩"
  case VClo(x, b, _) => s"⟨closure: λ$x.\n${pprint(b, 1)}⟩"
  case VNum(i) => i.toString
  case VBool(b) => b.toString
  case VUnit => "()"
