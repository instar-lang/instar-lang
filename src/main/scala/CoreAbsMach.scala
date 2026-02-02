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

enum Value:
  case VUnit
  case VNum(i: Int)
  case VBool(b: Boolean)
  case VClo(x: String, body: Expr, ρ: Env)
  case VCode(e: Expr) // XXX: could extend to open code value with environment?

import Stage.*
import Expr.*
import Value.*

type Env = Map[String, Value]
