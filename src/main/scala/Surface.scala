package spmp.surf

type StageVar = String
type BinOp = String

// Now we only have two stages: S0 and S1. SVar is the abstraction over them
enum Stage:
  case S0
  case S1
  case SVar(x: StageVar)

// TODO: not sure if we need to distinguish Type in Surface and Core.
// For now, we just add a Ty here for the surface language, Ty maybe will be merged into same Type in Core later.
enum Ty:
  // This definition is copied from the draft.
  case TUnit(stage: Stage)
  case TNat(stage: Stage)
  case TBool(stage: Stage)
  case TArrow(arg: Ty, stage: Stage, ret: Ty)
  case TRef(stage: Stage, inner: Ty)
  case TForAllS(s: StageVar, body: Ty)

enum Expr:
  case EUnit // ()
  case ENatV(n: Int) // n
  case EVar(x: String) // x

  case ELam(x: String, ty: Ty, body: Expr) // λx:τ.t
  case ESLam(s: StageVar, body: Expr) // Λα.t

  case ELet(x: String, rhs: Expr, body: Expr) // let x = t1 in t2

  case ELift(e: Expr) // lift t
  case ERun(e: Expr) // run t

  case EApp(e1: Expr, e2: Expr) // t1 t2
  case ESApp(e: Expr, s: Stage) // t[s]
  case EFix(f: String, e: Expr) // fix t

  case EIfz(cond: Expr, thn: Expr, els: Expr) // ifz t1 t2 t3
  case EIf(cond: Expr, thn: Expr, els: Expr) // if t1 t2 t3

  case EBin(op: BinOp, left: Expr, right: Expr) // t1 ⊕ t2

  case EAlloc(e: Expr) // alloc t
  case EGet(e: Expr) // get t
  case EPut(e1: Expr, e2: Expr) // put t1 t2

  case EAscribe(e: Expr, ty: Ty) // (t : τ)
