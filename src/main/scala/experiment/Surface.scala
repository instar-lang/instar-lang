package instar.experiment.surf

import instar.experiment.eff
import instar.experiment.eff.Type
import instar.experiment.eff.Stage

type StageVar = String
type BinOp = String

enum Expr:
  case EUnit // ()
  case ENatV(n: Int) // n
  case EVar(x: String) // x

  case ELam(x: String, ty: Type, body: Expr) // λx:τ.t
  case ESLam(s: StageVar, body: Expr) // Λα.t

  case ELet(x: String, rhs: Expr, body: Expr) // let x = t1 in t2

  case ELift(e: Expr, stage: Stage) // lift (t, s)
  case ERun(e: Expr) // run t

  case EApp(e1: Expr, e2: Expr) // t1 t2
  case ESApp(e: Expr, s: Stage) // t[s]
  case EFix(f: String, ty: Type, e: Expr) // fix t

  case EIfz(cond: Expr, thn: Expr, els: Expr) // ifz t1 t2 t3
  case EIf(cond: Expr, thn: Expr, els: Expr) // if t1 t2 t3

  case EBin(op: BinOp, left: Expr, right: Expr) // t1 ⊕ t2
  case EUnary(op: String, v: Expr) // ⊖ t

  case EAlloc(e: Expr) // alloc t
  case EGet(e: Expr) // get t
  case EPut(e1: Expr, e2: Expr) // put t1 t2

  case EAscribe(e: Expr, ty: Type) // (t : τ)
