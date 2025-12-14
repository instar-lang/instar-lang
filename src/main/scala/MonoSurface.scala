package spmp.surf.mono

import spmp.core.mono as core

enum Expr:
  case EUnit
  case ENum(i: Int)
  case EBool(b: Boolean)
  case EVar(name: String)
  case ELam(x: String, argTy: Option[core.Type], body: Expr, retTy: Option[core.Type])
  case EApp(e1: Expr, e2: Expr)
  case ELift(t: Expr)
  case ERun(t: Expr)
  case ELet(x: String, rhs: Expr, body: Expr)
  case ECond(e1: Expr, e2: Expr, e3: Expr)
  case EBinOp(op: String, e1: Expr, e2: Expr)
  case EUnaryOp(op: String, e: Expr)
  case EAscribe(e: Expr, asTy: core.Type)