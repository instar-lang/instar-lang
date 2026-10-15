package instar.experiment.eff

// On top of the Core language, additionally supports
// - mutable references
// - letrec for defining recursive functions

import instar.Counter.*

enum Stage:
  case SNum(n: Int)
  case SVar(x: String)

enum Type:
  case TUnit, TInt, TBool
  case TFun(t1: Type, t2: Type)
  case TRef(t: Type)
  case TForallSt(s: String, t: Type)
  case TAt(t: Type, s: Stage)
  case TCode(t: Type)

enum Expr:
  var ty: Option[Type] = None
  def withType(t: Type): Expr = { ty = Some(t); this }
  case EUnit
  case ENum(i: Int)
  case EBool(b: Boolean)
  case EVar(name: String)
  case ESLam(x: String, body: Expr)
  case ESApp(e: Expr, st: Stage)
  case ELam(x: String, argTy: Option[Type], body: Expr, retTy: Option[Type])
  case EApp(e1: Expr, e2: Expr, st: Stage)
  case ELift(t: Expr, to: Stage)
  case ERun(t: Expr)
  case ELet(x: String, rhs: Expr, body: Expr)
  case ELetRec(f: String, fnty: Type, rhs: Expr, body: Expr) // letrec f: ty = λx.e in e'
  case ECond(e1: Expr, e2: Expr, e3: Expr, st: Stage)
  case EBinOp(op: String, e1: Expr, e2: Expr, st: Stage)
  case EUnaryOp(op: String, e: Expr, st: Stage)
  case EAlloc(e: Expr, st: Stage)
  case EDeref(e: Expr, st: Stage)
  case EAssign(e1: Expr, e2: Expr, st: Stage)
  case EAscribe(e: Expr, asTy: Type)
  case EFix(f: String, e: Expr, st: Stage)
  case ELoc(l: Loc)

val Sta = Stage.SNum(0)
val Dyn = Stage.SNum(1)

def ENum1(i: Int): Expr = ENum(i)
def ENum2(i: Int): Expr = ELift2(ENum(i))
def EBool1(b: Boolean): Expr = EBool(b)
def EBool2(b: Boolean): Expr = ELift2(EBool(b))
def EApp1(e1: Expr, e2: Expr): Expr = EApp(e1, e2, Sta)
def EApp2(e1: Expr, e2: Expr): Expr = EApp(e1, e2, Dyn)
def ECond1(e1: Expr, e2: Expr, e3: Expr): Expr = ECond(e1, e2, e3, Sta)
def ECond2(e1: Expr, e2: Expr, e3: Expr): Expr = ECond(e1, e2, e3, Dyn)
def EBinOp1(op: String, e1: Expr, e2: Expr): Expr = EBinOp(op, e1, e2, Sta)
def EBinOp2(op: String, e1: Expr, e2: Expr): Expr = EBinOp(op, e1, e2, Dyn)
def EUnaryOp1(op: String, e: Expr): Expr = EUnaryOp(op, e, Sta)
def EUnaryOp2(op: String, e: Expr): Expr = EUnaryOp(op, e, Dyn)
def EAlloc1(e: Expr): Expr = EAlloc(e, Sta)
def EAlloc2(e: Expr): Expr = EAlloc(e, Dyn)
def EDeref1(e: Expr): Expr = EDeref(e, Sta)
def EDeref2(e: Expr): Expr = EDeref(e, Dyn)
def EAssign1(e1: Expr, e2: Expr): Expr = EAssign(e1, e2, Sta)
def EAssign2(e1: Expr, e2: Expr): Expr = EAssign(e1, e2, Dyn)

// Note: they lift term to stage 1/2, but lift itself can only be at stage 1
def ELift1(e: Expr): Expr = ELift(e, Sta)
def ELift2(e: Expr): Expr = ELift(e, Dyn)

enum Value:
  case VUnit
  case VNum(i: Int)
  case VBool(b: Boolean)
  case VLoc(loc: Loc)
  case VSClo(st: String, body: Expr, ρ: Env, ς: StEnv)
  case VClo(x: String, argTy: Option[Type], body: Expr, retTy: Option[Type], ρ: Env, ς: StEnv)
  case VCode(t: Expr) // XXX: could extend to open code value with environment?

extension (t: Option[Type])
  // Assuming well-formedness of types
  def erase: Option[Type] =
    t match
      case Some(TCode(t1)) => Some(t1)
      case _ => t

import Stage.*
import Expr.*
import Type.*
import Value.*

type Loc = Int
type Env = Map[String, Loc]
type Store = Map[Loc, Value]
type StEnv = Map[String, Stage]

type Cont = (Value, Store, MCont) => (Value, Store)
type MCont = (Value, Store) => (Value, Store)

def reflect(e: Expr, σ: Store, k: Cont, γ: MCont): (Value, Store) =
  e match
    // Note: here we decide what needs to be let-inserted based on syntactic form.
    // We could also avoid let-inserting for λ-terms and fix as they are pure.
    case EUnit | ENum(_) | EBool(_) => k(VCode(e), σ, γ)
    case _ =>
      val x = fresh()
      // In reduction semantics, we have the let-insertion rule
      // P[E[reflect t]] -> P[let x = t in E[x]].
      // Here, the continuation k is the E context, and γ is the P context.
      k(VCode(EVar(x)), σ, { case (VCode(t), σ1) =>
        γ(VCode(ELet(x, e, t)), σ1)
      })

def reify(e: Expr, ρ: Env, ς: StEnv, σ: Store, γ: MCont): (Value, Store) =
  eval(e, ρ, ς, σ, (x, σ1, γ1) => γ1(x, σ1), γ)

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

def evalStVar(s: Stage, ς: StEnv): Stage =
  s match
    case SVar(st) => ς(st)
    case _ => s

def lift(k: Cont)(v: Value, σ: Store, γ: MCont): (Value, Store) = v match
  case VUnit => reflect(EUnit, σ, k, γ)
  case VNum(i) => reflect(ENum(i), σ, k, γ)
  case VBool(b) => reflect(EBool(b), σ, k, γ)
  case VLoc(l) => reflect(ELoc(l), σ, k, γ)
  case VClo(x, argTy, body, retTy, ρf, ςf) =>
    val l = σ.size
    val y = fresh()
    reify(body, ρf + (x -> l), ςf, σ + (l -> VCode(EVar(y))), {
      case (VCode(t), σ2) =>
        reflect(ELam(y, argTy.erase, t, retTy.erase), σ2, k, γ)
    })

// FIXME: fst-stage side effect will break semantics-preservation.
def eval(e: Expr, ρ: Env, ς: StEnv, σ: Store, k: Cont, γ: MCont): (Value, Store) =
  e match
    case EUnit =>
      k(VUnit, σ, γ)
    case ENum(i) =>
      k(VNum(i), σ, γ)
    case EBool(b) =>
      k(VBool(b), σ, γ)
    case ELoc(l) =>
      k(VLoc(l), σ, γ)
    case EVar(x) =>
      k(σ(ρ(x)), σ, γ)
    case ESLam(x, body) =>
      k(VSClo(x, body, ρ, ς), σ, γ)
    case ESApp(e, st) =>
      eval(e, ρ, ς, σ, { case (VSClo(x, body, ρf, ςf), σ1, γ1) =>
        eval(body, ρf, ςf + (x -> evalStVar(st, ς)), σ1, k, γ1)
      }, γ)
    case ELam(x, argTy, e, retTy) =>
      k(VClo(x, argTy, e, retTy, ρ, ς), σ, γ)
    case EApp(e1, e2, s) if evalStVar(s, ς) == Sta =>
      eval(e1, ρ, ς, σ, { case (VClo(x, _, body, _, ρf, ςf), σ1, γ1) =>
        eval(e2, ρ, ς, σ1, (v2, σ2, γ2) =>
          val l = σ2.size
          eval(body, ρf + (x -> l), ςf, σ2 + (l -> v2), k, γ2), γ1)
      }, γ)
    case EApp(e1, e2, s) if evalStVar(s, ς) == Dyn =>
      eval(e1, ρ, ς, σ, { case (VCode(x1), σ1, γ1) =>
        eval(e2, ρ, ς, σ1, { case (VCode(x2), σ2, γ2) =>
          reflect(EApp1(x1, x2), σ2, k, γ2)
        }, γ1)
      }, γ)
    case ELift(e, to) if evalStVar(to, ς) == Sta =>
      eval(e, ρ, ς, σ, k, γ)
    case ELift(e, to) if evalStVar(to, ς) == Dyn =>
      eval(e, ρ, ς, σ, lift(k), γ)
    case ERun(e) =>
      reify(e, ρ, ς, σ, { case (VCode(t), σ2) =>
        // Note: here we allow cross-stage persistence!
        eval(t, Map(), Map(), σ2, k, γ)
      })
    case ELet(x, rhs, e) =>
      eval(rhs, ρ, ς, σ, (v, σ1, γ1) =>
        val l = σ1.size
        eval(e, ρ + (x -> l), ς, σ1 + (l -> v), k, γ1), γ)
    case ELetRec(f, _, rhs, e) =>
      eval(rhs, ρ, ς, σ, {
        case (VClo(x, argTy, body, retTy, ρf, ςf), σ1, γ1) =>
          val l = σ1.size
          val ρf1 = ρf + (f -> l)
          val v = VClo(x, argTy, body, retTy, ρf1, ςf)
          eval(e, ρ + (f -> l), ς, σ1 + (l -> v), k, γ1)
        case (VSClo(x, body, ρf, ςf), σ1, γ1) =>
          val l = σ1.size
          val ρf1 = ρf + (f -> l)
          val v = VSClo(x, body, ρf1, ςf)
          eval(e, ρ + (f -> l), ς, σ1 + (l -> v), k, γ1)
      }, γ)
    case ECond(e1, e2, e3, s) if evalStVar(s, ς) == Sta =>
      eval(e1, ρ, ς, σ, { case (VBool(b), σ1, γ1) =>
        if b then eval(e2, ρ, ς, σ1, k, γ1)
        else eval(e3, ρ, ς, σ1, k, γ1)
      }, γ)
    case ECond(e1, e2, e3, s) if evalStVar(s, ς) == Dyn =>
      eval(e1, ρ, ς, σ, { case (VCode(x1), σ1, γ1) =>
        reify(e2, ρ, ς, σ1, { case (VCode(x2), σ2) =>
          reify(e3, ρ, ς, σ2, { case (VCode(x3), σ3) =>
            reflect(ECond1(x1, x2, x3), σ3, k, γ1)
          })
        })
      }, γ)
    case EBinOp(op, e1, e2, s) if evalStVar(s, ς) == Sta =>
      eval(e1, ρ, ς, σ, { case (v1, σ1, γ1) =>
        eval(e2, ρ, ς, σ1, { case (v2, σ2, γ2) =>
          k(evalPrim(op, v1, v2), σ2, γ2)
        }, γ1)
      }, γ)
    case EBinOp(op, e1, e2, s) if evalStVar(s, ς) == Dyn =>
      eval(e1, ρ, ς, σ, { case (VCode(x1), σ1, γ1) =>
        eval(e2, ρ, ς, σ1, { case (VCode(x2), σ2, γ2) =>
          reflect(EBinOp1(op, x1, x2), σ2, k, γ2)
        }, γ1)
      }, γ)
    case EUnaryOp(op, e, s) if evalStVar(s, ς) == Sta =>
      eval(e, ρ, ς, σ, { case (v, σ1, γ1) =>
        k(evalPrimUnary(op, v), σ1, γ1)
      }, γ)
    case EUnaryOp(op, e, s) if evalStVar(s, ς) == Dyn =>
      eval(e, ρ, ς, σ, { case (VCode(x), σ1, γ1) =>
        reflect(EUnaryOp1(op, x), σ1, k, γ1)
      }, γ)
    case EAlloc(e, s) if evalStVar(s, ς) == Sta =>
      eval(e, ρ, ς, σ, { case (v, σ1, γ1) =>
        val l = σ1.size
        k(VLoc(l), σ1 + (l -> v), γ1)
      }, γ)
    case EAlloc(e, s) if evalStVar(s, ς) == Dyn =>
      eval(e, ρ, ς, σ, { case (VCode(x), σ1, γ1) =>
        reflect(EAlloc1(x), σ1, k, γ1)
      }, γ)
    case EDeref(e, s) if evalStVar(s, ς) == Sta =>
      eval(e, ρ, ς, σ, { case (VLoc(l), σ1, γ1) =>
        k(σ1(l), σ1, γ1)
      }, γ)
    case EDeref(e, s) if evalStVar(s, ς) == Dyn =>
      eval(e, ρ, ς, σ, { case (VCode(x), σ1, γ1) =>
        reflect(EDeref1(x), σ1, k, γ1)
      }, γ)
    case EAssign(e1, e2, s) if evalStVar(s, ς) == Sta =>
      eval(e1, ρ, ς, σ, { case (VLoc(l), σ1, γ1) =>
        eval(e2, ρ, ς, σ1, { case (v2, σ2, γ2) =>
          k(VUnit, σ2 + (l -> v2), γ2)
        }, γ1)
      }, γ)
    case EAssign(e1, e2, s) if evalStVar(s, ς) == Dyn =>
      eval(e1, ρ, ς, σ, { case (VCode(x1), σ1, γ1) =>
        eval(e2, ρ, ς, σ1, { case (VCode(x2), σ2, γ2) =>
          reflect(EAssign1(x1, x2), σ2, k, γ2)
        }, γ1)
      }, γ)
    case EAscribe(e, _) => eval(e, ρ, ς, σ, k, γ)
    case EFix(f, e, s) if evalStVar(s, ς) == Sta =>
      eval(e, ρ, ς, σ, {
        case (VClo(x, argTy, body, retTy, ρf, ςf), σ1, γ1) =>
          val l = σ1.size
          val v = VClo(x, argTy, body, retTy, ρf + (f -> l), ςf)
          k(v, σ1 + (l -> v), γ1)
        case (VSClo(x, body, ρf, ςf), σ1, γ1) =>
          val l = σ1.size
          val v = VSClo(x, body, ρf + (f -> l), ςf)
          k(v, σ1 + (l -> v), γ1)
      }, γ)
    case EFix(f, e, s) if evalStVar(s, ς) == Dyn =>
      val l = σ.size
      val ρ1 = ρ + (f -> l)
      val g = fresh("f")
      val σ1 = σ + (l -> VCode(EVar(g)))
      reify(e, ρ1, ς, σ1, { case (VCode(x), σ2) =>
        reflect(EFix(g, x, Sta), σ2, k, γ)
      })

def eval(e: Expr): (Value, Store) =
  clear
  eval(e, Map(), Map(), Map(), (x, σ, γ) => γ(x, σ), (x, σ) => (x, σ))