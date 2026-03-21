package instar.tyck

/*

import instar.eff.opt
import instar.eff.opt.Type
import instar.eff.opt.Stage

import instar.surf.*

type Env = Map[String, Type]

def infer(env: Env, expr: Expr): Expr =
  expr match
    case Expr.EUnit                 =>
    case Expr.ENatV(n)              =>
    case Expr.EVar(x)               =>
    case Expr.ELam(x, ty, body)     =>
    case Expr.ESLam(s, body)        =>
    case Expr.ELet(x, rhs, body)    =>
    case Expr.ELift(e)              =>
    case Expr.ERun(e)               =>
    case Expr.EApp(e1, e2)          =>
    case Expr.ESApp(e, s)           =>
    case Expr.EFix(f, ty, e)        =>
    case Expr.EIfz(cond, thn, els)  =>
    case Expr.EIf(_, _, _)          => ???
    case Expr.EBin(op, left, right) =>
    case Expr.EAlloc(e)             =>
    case Expr.EGet(e)               =>
    case Expr.EPut(e1, e2)          =>
    case Expr.EAscribe(e, ty)       =>
  ???

def check(env: Env, term: Expr, expected: Type): Expr =
  term match
    case Expr.EUnit                 =>
    case Expr.ENatV(n)              =>
    case Expr.EVar(x)               =>
    case Expr.ELam(x, ty, body)     =>
    case Expr.ESLam(s, body)        =>
    case Expr.ELet(x, rhs, body)    =>
    case Expr.ELift(e)              =>
    case Expr.ERun(e)               =>
    case Expr.EApp(e1, e2)          =>
    case Expr.ESApp(e, s)           =>
    case Expr.EFix(f, ty, e)        =>
    case Expr.EIfz(cond, thn, els)  =>
    case Expr.EIf(_, _, _)          =>
    case Expr.EBin(op, left, right) =>
    case Expr.EAlloc(e)             =>
    case Expr.EGet(e)               =>
    case Expr.EPut(e1, e2)          =>
    case Expr.EAscribe(e, ty)       =>
  ???

*/