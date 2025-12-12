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
  case TArrow(from: Ty, stage: Stage, to: Ty)
  case TRef(stage: Stage, inner: Ty)
  case TForAll(a: StageVar, body: Ty)

enum Expr:
  case EUnit // ()
  case ENatV(n: Int) // n
  case EVar(x: String) // x

  case ELam(x: String, tpe: Ty, body: Expr) // λx:τ.t
  case ESLam(a: StageVar, body: Expr) // Λα.t

  case ELet(x: String, rhs: Expr, body: Expr) // let x = t1 in t2

  case ELift(t: Expr) // lift t
  case ERun(t: Expr) // run t

  case EApp(fun: Expr, arg: Expr) // t1 t2
  case ESApp(t: Expr, s: Stage) // t[s]
  case EFix(t: Expr) // fix t

  case EIfz(cond: Expr, thn: Expr, els: Expr) // ifz t1 t2 t3

  case EBin(op: BinOp, left: Expr, right: Expr) // t1 ⊕ t2

  case EAlloc(t: Expr) // alloc t
  case EGet(t: Expr) // get t
  case EPut(loc: Expr, value: Expr) // put t1 t2

  case EAscribe(t: Expr, tpe: Ty) // (t : τ)
