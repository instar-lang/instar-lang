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
  // case TCode(t: Type)
  case TFrag(t: Type)
  /*
  Note: the terms with rep type are only constructed by:
  * λ|2|'s administrative typing rules, such as lam𝕔, code and lets𝕔.
  * λ|2|'s T-REP typing rules, lift the frag type into rep type.
  Note: the terms with rep type are only used in λ|2|'s ifz² typing rules：
  Γ ⊢ e₁ : frag nat | ϵ₁
  Γ ⊢ e₂ : rep nat | ϵ₂
  Γ ⊢ e₃ : rep nat | ϵ₃
  —————————————————————————————————
  Γ ⊢ ifz² e₁ e₂ e₃ : frag nat | ⊤
  */
  case TRep(t : Type)

enum Expr:
  var ty: Option[Type] = None
  def withType(t: Type): Expr = { ty = Some(t); this }
  case EUnit
  case ENum(i: Int)
  case EBool(b: Boolean)
  case EVar(name: String)
  // case ESLam(x: String, body: Expr)
  // case ESApp(e: Expr, st: Stage)
  case ELam(x: String, argTy: Option[Type], body: Expr, retTy: Option[Type])
  case EApp(e1: Expr, e2: Expr, st: Stage)
  // Note: they can only lift terms to the dyn stage.
  // case ELift(t: Expr, to: Stage)
  case ELift(t: Expr)
  case ERun(t: Expr)
  case ELet(x: String, rhs: Expr, body: Expr)
  case ECond(e1: Expr, e2: Expr, e3: Expr, st: Stage)
  case EBinOp(op: String, e1: Expr, e2: Expr, st: Stage)
  case EUnaryOp(op: String, e: Expr, st: Stage)
  // TODO: move this into withType?
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
  case VClo(x: String, argTy: Option[Type], body: Expr, retTy: Option[Type], ρ: Env)
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