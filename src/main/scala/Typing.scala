package spmp.tyck

import spmp.core
import spmp.surf.*

type Env = Map[String, core.Type]

def infer(term: Expr): core.Expr =
  term match
    case Expr.EUnit                 =>
    case Expr.ENatV(n)              =>
    case Expr.EVar(x)               =>
    case Expr.ELam(x, tpe, body)    =>
    case Expr.ESLam(a, body)      =>
    case Expr.ELet(x, rhs, body)    =>
    case Expr.ELift(t)              =>
    case Expr.ERun(t)               =>
    case Expr.EApp(fun, arg)        =>
    case Expr.ESApp(t, s)       =>
    case Expr.EFix(t)               =>
    case Expr.EIfz(cond, thn, els)  =>
    case Expr.EBin(op, left, right) =>
    case Expr.EAlloc(t)             =>
    case Expr.EGet(t)               =>
    case Expr.EPut(loc, value)      =>
    case Expr.EAscribe(t, tpe)      =>
  ???

def check(term: Expr, expected: core.Type): core.Expr =
  term match
    case Expr.EUnit                 =>
    case Expr.ENatV(n)              =>
    case Expr.EVar(x)               =>
    case Expr.ELam(x, tpe, body)    =>
    case Expr.ESLam(a, body)      =>
    case Expr.ELet(x, rhs, body)    =>
    case Expr.ELift(t)              =>
    case Expr.ERun(t)               =>
    case Expr.EApp(fun, arg)        =>
    case Expr.ESApp(t, s)       =>
    case Expr.EFix(t)               =>
    case Expr.EIfz(cond, thn, els)  =>
    case Expr.EBin(op, left, right) =>
    case Expr.EAlloc(t)             =>
    case Expr.EGet(t)               =>
    case Expr.EPut(loc, value)      =>
    case Expr.EAscribe(t, tpe)      =>
  ???
