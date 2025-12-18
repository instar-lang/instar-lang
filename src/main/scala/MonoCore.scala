package spmp.core.mono

// On top of the Core language, removes the stage polymorphism feature.

import spmp.Counter.*

enum Stage:
  case SNum(n: Int)
  // case SVar(x: String)

enum Type:
  case TUnit, TInt, TBool
  case TFun(t1: Type, t2: Type)
  // case TForallSt(s: String, t: Type)
  // case TAt(t: Type, s: Stage)
  case TCode(t: Type)
  // case TFrag(t: Type)

  /* Note: the terms with rep type are only constructed by:
  1. λ|2|'s administrative typing rules, such as lam𝕔, code and lets𝕔.
  2. λ|2|'s T-REP typing rules, lift the frag type into rep type.
  */

  /* Note: the terms with rep type are only used in λ|2|'s ifz² typing rules：
  Γ ⊢ e₁ : frag nat | ϵ₁
  Γ ⊢ e₂ : rep τ | ϵ₂
  Γ ⊢ e₃ : rep τ | ϵ₃
  ———————————————————————————————
  Γ ⊢ ifz² e₁ e₂ e₃ : frag τ | ⊤
  */
  // case TRep(t : Type)

enum Expr:
  var ty: Option[Type] = None
  def withType(t: Type): Expr = { ty = Some(t); this }
  case EUnit
  case ENum(i: Int)
  case EBool(b: Boolean)
  case EVar(name: String)
  // case ESLam(x: String, body: Expr)
  // case ESApp(e: Expr, st: Stage)
  // Note: are argTy and retTy still necessary here? They could be found in Expr.ty.
  // case ELam(x: String, argTy: Option[Type], body: Expr, retTy: Option[Type])
  case ELam(x: String, body: Expr)
  case EApp(e1: Expr, e2: Expr, st: Stage)
  // Note: they can only lift terms to the dyn stage.
  // case ELift(t: Expr, to: Stage)
  case ELift(t: Expr)
  case ERun(t: Expr)
  case ELet(x: String, rhs: Expr, body: Expr)
  case ECond(e1: Expr, e2: Expr, e3: Expr, st: Stage)
  case EBinOp(op: String, e1: Expr, e2: Expr, st: Stage)
  case EUnaryOp(op: String, e: Expr, st: Stage)
  // TODO: move this into Expr.ty?
  case EAscribe(e: Expr, asTy: Type)

val Sta = Stage.SNum(0)
val Dyn = Stage.SNum(1)

def EApp1(e1: Expr, e2: Expr): Expr = EApp(e1, e2, Sta)
def EApp2(e1: Expr, e2: Expr): Expr = EApp(e1, e2, Dyn)
def ECond1(e1: Expr, e2: Expr, e3: Expr): Expr = ECond(e1, e2, e3, Sta)
def ECond2(e1: Expr, e2: Expr, e3: Expr): Expr = ECond(e1, e2, e3, Dyn)
def EBinOp1(op: String, e1: Expr, e2: Expr): Expr = EBinOp(op, e1, e2, Sta)
def EBinOp2(op: String, e1: Expr, e2: Expr): Expr = EBinOp(op, e1, e2, Dyn)
def EUnaryOp1(op: String, e: Expr): Expr = EUnaryOp(op, e, Sta)
def EUnaryOp2(op: String, e: Expr): Expr = EUnaryOp(op, e, Dyn)

enum Value:
  case VUnit
  case VNum(i: Int)
  case VBool(b: Boolean)
  // case VSClo(st: String, body: Expr, ρ: Env, ς: StEnv)
  // case VClo(x: String, argTy: Option[Type], body: Expr, retTy: Option[Type], ρ: Env, ς: StEnv)
  case VClo(x: String, body: Expr, ρ: Env)
  case VCode(e: Expr) // XXX: could extend to open code value with environment?

import Stage.*
import Expr.*
import Type.*
import Value.*

type Env = Map[String, Value]
// type StEnv = Map[String, Stage]
type Ans = Value

type Cont = (Value, MCont) => Value
type MCont = Value => Value

def reflect(e: Expr, k: Cont, γ: MCont): Value =
  e match
    // Note: here we decide what needs to be let-inserted based on syntactic form.
    // We could also avoid let-inserting for λ-terms and fix as they are pure.
    case EUnit | ENum(_) | EBool(_) => k(VCode(e), γ)
    case _ =>
      val x = fresh()
      // In reduction semantics, we have the let-insertion rule
      // P[E[reflect e]] -> P[let x = e in E[x]].
      // Here, the continuation k is the E context, and γ is the P context.
      k(VCode(EVar(x)), { case VCode(t) =>
        // Note: our type system must ensure that γ has type rep τ₀ → τ₁,
        // otherwise the pattern matching would fail.
        γ(VCode(ELet(x, e, t)))
      })

def reify(e: Expr, ρ: Env, γ: MCont): Value =
  eval(e, ρ, (x, γ1) => γ1(x), γ)

def lift(k: Cont)(v: Value, γ: MCont): Value =
  v match
    case VUnit => reflect(EUnit, k, γ)
    case VNum(i) => reflect(ENum(i), k, γ)
    case VBool(b) => reflect(EBool(b), k, γ)
    case VClo(x, body, ρf) =>
      val y = fresh()
      reify(body, ρf + (x -> VCode(EVar(y))), { case VCode(t) =>
        reflect(ELam(y, t), k, γ)
      })

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

def eval(e: Expr, ρ: Env, k: Cont, γ: MCont): Value =
  e match
    case EUnit =>
      k(VUnit, γ)
    case ENum(i) =>
      k(VNum(i), γ)
    case EBool(b) =>
      k(VBool(b), γ)
    case EVar(x) =>
      k(ρ(x), γ)
    case ELam(x, e) =>
      k(VClo(x, e, ρ), γ)
    case EApp(e1, e2, s) if s == Sta =>
      eval(e1, ρ, { case (VClo(x, body, ρf), γ1) =>
        eval(e2, ρ, (v2, γ2) =>
          eval(body, ρf + (x -> v2), k, γ2), γ1)
      }, γ)
    case EApp(e1, e2, s) if s == Dyn =>
      eval(e1, ρ, { case (VCode(x1), γ1) =>
        eval(e2, ρ, { case (VCode(x2), γ2) =>
          reflect(EApp1(x1, x2), k, γ2)
        }, γ1)
      }, γ)
    case ELift(e) =>
      eval(e, ρ, lift(k), γ)
    case ERun(e) =>
      eval(e, ρ, { case (VCode(t), γ1) =>
        eval(t, ρ, k, γ1)
      }, γ)
    case ELet(x, rhs, e) =>
      eval(rhs, ρ, (v, γ1) => eval(e, ρ + (x -> v), k, γ1), γ)
    case ECond(e1, e2, e3, s) if s == Sta =>
      eval(e1, ρ, { case (VBool(b), γ1) =>
        if b then eval(e2, ρ, k, γ1)
        else eval(e3, ρ, k, γ1)
      }, γ)
    case ECond(e1, e2, e3, s) if s == Dyn =>
      eval(e1, ρ, { case (VCode(x1), γ1) =>
        reify(e2, ρ, { case VCode(x2) =>
          reify(e3, ρ, { case VCode(x3) =>
            reflect(ECond1(x1, x2, x3), k, γ1)
          })
        })
      }, γ)
    case EBinOp(op, e1, e2, s) if s == Sta =>
      eval(e1, ρ, { case (v1, γ1) =>
        eval(e2, ρ, { case (v2, γ2) =>
          k(evalPrim(op, v1, v2), γ2)
        }, γ1)
      }, γ)
    case EBinOp(op, e1, e2, s) if s == Dyn =>
      eval(e1, ρ, { case (VCode(x1), γ1) =>
        eval(e2, ρ, { case (VCode(x2), γ2) =>
          reflect(EBinOp1(op, x1, x2), k, γ2)
        }, γ1)
      }, γ)
    case EUnaryOp(op, e, s) if s == Sta =>
      eval(e, ρ, { case (v, γ1) =>
        k(evalPrimUnary(op, v), γ1)
      }, γ)
    case EUnaryOp(op, e, s) if s == Dyn =>
      eval(e, ρ, { case (VCode(x), γ1) =>
        reflect(EUnaryOp1(op, x), k, γ1)
      }, γ)
    case EAscribe(e, _) => eval(e, ρ, k, γ)

def eval(e: Expr): Ans =
  reset
  eval(e, Map(), (x, γ) => γ(x), x => x)