package instar.interp

// On top of the Core language, additionally supports
// - mutable references
// - letrec/fix for defining recursive functions

// On top if the CoreEff, additionally supports optimizations:
// - dead code elimination
//   how: before let-inserting, check if the bound variable is used in the body
//   only for pure expressions.
// - rewriting (constant folding, inlining)
//   how: when we do reflect, we simplify the expression
//   for function inlining (β-inline), we need to renormalize function body
// - common subexpression elimination (only for pure expressions)
//   how: add a cache Map[Expr, Var] when reifying, need to carefully control the scope of the cache
// - TODO: code motion
//     let-floating https://dl.acm.org/doi/10.1145/232627.232630
// - TODO: lambda lifting https://link.springer.com/chapter/10.1007/3-540-45788-7_8
// - TODO: deforestation, loop fusion, and domain-specific optimizations

import instar.syntax.*
import instar.Counter.*
import instar.BiMap
import collection.mutable.HashSet

enum Value:
  case VUnit
  case VNum(i: Int)
  case VBool(b: Boolean)
  case VLoc(loc: Loc)
  case VSClo(st: String, body: Expr, ρ: Env, ς: StEnv)
  case VClo(x: String, argTy: Option[Type], body: Expr, retTy: Option[Type], ρ: Env, ς: StEnv)
  case VBNClo(x: String, argTy: Option[Type], body: Expr, retTy: Option[Type], ρ: Env, ς: StEnv)
  case VCode(t: Expr) // XXX: could extend to open code value with environment?
  case VThunk(e: Expr, ρ: Env, ς: StEnv)

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

type Env = Map[String, Loc]
type Store = Map[Loc, Value]
type StEnv = Map[String, Stage]
type Cache = BiMap[Expr, String]

type Cont = (Value, Store, MCont) => Cache ?=> (Value, Store)
type MCont = (Value, Store) => (Value, Store)

type ⇀[A, B] = PartialFunction[A, B]

object Opt:
  // Supported optimizations:
  // - rewriting
  // - dce
  // - no-let-lam
  // - fun-inline
  // - simp-cond
  val opt: HashSet[String] = HashSet()
  def apply(id: String): Boolean = opt.contains(id)
  def enable(id: String*): Unit =
    opt.clear
    opt.addAll(id)
  def disable(id: String): Unit = opt.remove(id)
  def disableAll: Unit = opt.clear

extension (e: Expr)
  def isPure: Boolean =
    e match
      case EUnit | ENum(_) | EBool(_) | EVar(_) => true
      case ESLam(_, _) | ELam(_, _, _, _) | EBNLam(_, _, _, _) => true
      case EBinOp(_, _, _, _) | EUnaryOp(_, _, _) => true
      case ESApp(_, _) | EApp(_, _, _) => false
      case ELift(t, _) => false
      case EAlloc(_, _) | EDeref(_, _) | EAssign(_, _, _) => false
      case ERun(t) => t.isPure
      case ELet(_, rhs, body) => rhs.isPure && body.isPure
      case ELetRec(_, rhs, body) => rhs.isPure && body.isPure
      case ECond(e1, e2, e3, _) => e1.isPure && e2.isPure && e3.isPure
      case EAscribe(e, _) => e.isPure
      case EFix(_, e, _) => e.isPure
      case _ => false

  def freeVar: Set[String] =
    e match
      case EUnit | ENum(_) | EBool(_) => Set()
      case EVar(x) => Set(x)
      case ESLam(x, body) => body.freeVar
      case ESApp(e, _) => e.freeVar
      case ELam(x, _, body, _) => body.freeVar - x
      case EApp(e1, e2, _) => e1.freeVar ++ e2.freeVar
      case ECBNApp(e1, e2) => e1.freeVar ++ e2.freeVar
      case ELift(t, _) => t.freeVar
      case ERun(t) => t.freeVar
      case ELet(x, rhs, body) => rhs.freeVar ++ (body.freeVar - x)
      case ELetRec(f, rhs, body) => (rhs.freeVar - f) ++ (body.freeVar - f)
      case ECond(e1, e2, e3, _) => e1.freeVar ++ e2.freeVar ++ e3.freeVar
      case EBinOp(_, e1, e2, _) => e1.freeVar ++ e2.freeVar
      case EUnaryOp(_, e, _) => e.freeVar
      case EAlloc(e, _) => e.freeVar
      case EDeref(e, _) => e.freeVar
      case EAssign(e1, e2, _) => e1.freeVar ++ e2.freeVar
      case EAscribe(e, _) => e.freeVar
      case EFix(f, e, _) => e.freeVar - f

  // We only use this function to substitute the binding variable with the argument (which is always a pure, atomic expression),
  // and all variables after reflect are distinct, so we do not need to consider variable capture here.
  def subst(from: String, to: Expr): Expr =
    e match
      case EUnit | ENum(_) | EBool(_) => e
      case EVar(x) => if x == from then to else e
      case ESLam(x, body) => ESLam(x, body.subst(from, to))
      case ESApp(e, st) => ESApp(e.subst(from, to), st)
      case ELam(x, argTy, body, retTy) =>
        ELam(x, argTy, body.subst(from, to), retTy)
      case EApp(e1, e2, st) => EApp(e1.subst(from, to), e2.subst(from, to), st)
      case ELift(t, s) => ELift(t.subst(from, to), s)
      case ERun(t) => ERun(t.subst(from, to))
      case ELet(x, rhs, body) =>
        ELet(x, rhs.subst(from, to), body.subst(from, to))
      case ELetRec(f, rhs, body) =>
        ELetRec(f, rhs.subst(from, to), body.subst(from, to))
      case ECond(e1, e2, e3, s) =>
        ECond(e1.subst(from, to), e2.subst(from, to), e3.subst(from, to), s)
      case EBinOp(op, e1, e2, s) => EBinOp(op, e1.subst(from, to), e2.subst(from, to), s)
      case EUnaryOp(op, e, s) => EUnaryOp(op, e.subst(from, to), s)
      case EAlloc(e, s) => EAlloc(e.subst(from, to), s)
      case EDeref(e, s) => EDeref(e.subst(from, to), s)
      case EAssign(e1, e2, s) => EAssign(e1.subst(from, to), e2.subst(from, to), s)
      case EAscribe(e, asTy) => EAscribe(e.subst(from, to), asTy)
      case EFix(f, e, s) =>
        EFix(f, e.subst(from, to), s)

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

def evalExprStage(s: Option[Stage], ς: StEnv): Stage =
  s match
    case Some(st) => evalStVar(st, ς)
    case None => Sta

object StaticLam:
  def unapply(e: Expr)(using c: Cache): Option[ELam] =
    e match
      case e@ELam(_, _, _, _) => Some(e)
      case EVar(f) if c.inv.contains(f) => StaticLam.unapply(c.inv(f))
      case _ => None

object StaticConst:
  def unapply(e: Expr)(using c: Cache): Option[Value] =
    e match
      case ENum(i) => Some(VNum(i))
      case EBool(b) => Some(VBool(b))
      case EVar(x) if c.inv.contains(x) => StaticConst.unapply(c.inv(x))
      case _ => None

def renormalize(e: Expr, σ: Store, k: Cont, γ: MCont)(using c: Cache): (Value, Store) = e match
  case ELet(x, rhs, body) =>
    reflect(rhs, σ, { case (VCode(t), σ1, γ1) =>
      renormalize(body.subst(x, t), σ1, k, γ1)
    }, γ)
  case _ => k(VCode(e), σ, γ)

def reflectAtom(σ: Store, k: Cont, γ: MCont)(using c: Cache): Expr ⇀ (Value, Store) =
  case EUnit => k(VCode(EUnit), σ, γ)
  case ENum(i) => k(VCode(ENum(i)), σ, γ)
  case EBool(b) => k(VCode(EBool(b)), σ, γ)

def reflectLam(σ: Store, k: Cont, γ: MCont)(using c: Cache): Expr ⇀ (Value, Store) =
  case e@ELam(_, _, _, _) if Opt("no-let-lam") =>
    k(VCode(e), σ, γ)

// TODO: we want to simplify 2 + (3 + x) to be 5 + x as well,
// a few ideas:
// - borrowing ideas from Yallop's Partially-Static Data as Free Extension of Algebras
// - integrate equality saturation based simplification
// Note: technically we could use reify here, but seems a bit overkill
def reflectSimp(σ: Store, k: Cont, γ: MCont)(using c: Cache): Expr ⇀ (Value, Store) =
  case EBinOp(op, StaticConst(v1), StaticConst(v2), _) if Opt("rewriting") =>
    evalPrim(op, v1, v2) match
      case VNum(i) => reflect(ENum(i), σ, k, γ)
      case VBool(b) => reflect(EBool(b), σ, k, γ)

def reflectInline(σ: Store, k: Cont, γ: MCont)(using c: Cache): Expr ⇀ (Value, Store) =
  case EApp(StaticLam(ELam(x, _, body, _)), arg, _) if Opt("fun-inline") =>
    // Note: the function body is closed, as it may still refer to other second-stage variables,
    // so we cannot reuse reify to "partially evaluate" the body.
    // Naive inlining `reflect(body.subst(x, arg), σ, c, k, γ)` does not produce well-formed ANF.
    // We need to renormalize the body after substitution, but this can be O(n^2),
    // see Compiling with Continuations, Continued, Kennedy, ICFP 07.
    renormalize(body.subst(x, arg), σ, k, γ)

def reflectCondSimp(σ: Store, k: Cont, γ: MCont)(using c: Cache): Expr ⇀ (Value, Store) =
  case ECond(StaticConst(VBool(b)), e2, e3, _) if Opt("simp-cond") =>
    if b then renormalize(e2, σ, k, γ)
    else renormalize(e3, σ, k, γ)

object CachedExpr:
  def unapply(e: Expr)(using c: Cache): Option[EVar] =
    if (e.isPure && c.contains(e)) Some(EVar(c(e)))
    else None

def reflectCse(σ: Store, k: Cont, γ: MCont)(using c: Cache): Expr ⇀ (Value, Store) =
  case CachedExpr(x) if Opt("cse") =>
    k(VCode(x), σ, γ)

def reflectDce(σ: Store, k: Cont, γ: MCont)(using c: Cache): Expr ⇀ (Value, Store) =
  case e if Opt("dce") && e.isPure =>
    val x = fresh()
    k(VCode(EVar(x)), σ, { case (VCode(body), σ1) =>
      if (!body.freeVar(x)) γ(VCode(body), σ1)
      else γ(VCode(ELet(x, e, body)), σ1)
    })(using c + (e -> x))

def reflectDefault(σ: Store, k: Cont, γ: MCont)(using c: Cache): Expr ⇀ (Value, Store) =
  case e =>
    val x = fresh()
    k(VCode(EVar(x)), σ, {
      case (VCode(body), σ1) =>
        γ(VCode(ELet(x, e, body)), σ1)
    })(using c + (e -> x))

def reflect(e: Expr, σ: Store, k: Cont, γ: MCont)(using c: Cache): (Value, Store) =
  val funs = List(
    reflectAtom,
    reflectLam,
    reflectInline,
    reflectSimp,
    reflectCondSimp,
    reflectCse,
    reflectDce,
  )
  funs.foldRight(reflectDefault(σ, k, γ)) { (f, acc) => f(σ, k, γ).orElse(acc) }(e)

def reify(e: Expr, ρ: Env, ς: StEnv, σ: Store, γ: MCont)(using c: Cache): (Value, Store) =
  eval(e, ρ, ς, σ, (x, σ1, γ1) => γ1(x, σ1), γ)

def idK(v: Value, σ: Store, γ: MCont): (Value, Store) = γ(v, σ)

def hoistable(e: Expr)(using c: Cache): Boolean =
  e.isPure && e.freeVar.intersect(c.allVals).isEmpty

// TODO: how to handle if with two branches?
def hoist(e: Expr, σ: Store, k: Cont, γ: MCont)(using c: Cache): (Value, Store) =
  e match
    case ELet(x, rhs, body) if hoistable(rhs) =>
      println(s"Lift let-binding: $x = $rhs")
      // split hoisted lets into meta-continuation, body1 is supposed to be wrapped with ELam
      hoist(body, σ, k, { case (VCode(body1), σ1) =>
        γ(VCode(ELet(x, rhs, body1)), σ1)
      })(using c + (rhs -> x))
    case ELet(x, rhs, body) =>
      println(s"Sink let-binding: $x = $rhs")
      // split sunk lets into continuation
      hoist(body, σ, { case (VCode(body1), σ1, γ1) =>
        k(VCode(ELet(x, rhs, body1)), σ1, γ1)
      }, γ)(using c + (rhs -> x))
    case _ => k(VCode(e), σ, γ)

def lift(k: Cont)(v: Value, σ: Store, γ: MCont)(using c: Cache): (Value, Store) = v match
  case VUnit => reflect(EUnit, σ, k, γ)
  case VNum(i) => reflect(ENum(i), σ, k, γ)
  case VBool(b) => reflect(EBool(b), σ, k, γ)
  case VLoc(l) => reflect(ELoc(l), σ, k, γ)
  case VClo(x, argTy, body, retTy, ρf, ςf) =>
    val l = σ.size
    val y = fresh()
    reify(body, ρf + (x -> l), ςf, σ + (l -> VCode(EVar(y))), {
      case (VCode(t), σ2) =>
        if (Opt("lam-hoist"))
          hoist(t, σ2, { case (VCode(t1), σ3, γ1) =>
            println(s"Hoisted lambda body: $t1")
            reflect(ELam(y, argTy.erase, t1, retTy.erase), σ3, (v, σ3, γ1) => γ1(v, σ3), γ1)
          }, { case (VCode(t1), σ3) =>
            println(s"Hoisted whole term: $t1")
            // now we need to renormalize the whole term, as it may contain lifted bindings,
            // so we cannot directly pass it to the continuation, which would
            // expect variables/atomic expressions for ANF.
            renormalize(t1, σ3, k, γ)
          })(using BiMap((EVar(y) -> y)))
        else
          reflect(ELam(y, argTy.erase, t, retTy.erase), σ2, k, γ)
      })

def isApp(k: Cont)(v: Value, σ: Store, γ: MCont)(using c: Cache): (Value, Store) = v match
  case VCode(EVar(x)) =>
    c.inv(x) match
      case EApp(_, _, _) => k(VBool(true), σ, γ)
      case _ => k(VBool(false), σ, γ)
  case VCode(_) => k(VBool(false), σ, γ)

// Note: fst-stage side effect will break semantics-preservation,
// but we won't be handle/prevent that in the dynamic interpreter.
def eval(e: Expr, ρ: Env, ς: StEnv, σ: Store, k: Cont, γ: MCont)(using c: Cache): (Value, Store) =
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
      σ(ρ(x)) match
        case VThunk(e, ρ, ς) => eval(e, ρ, ς, σ, k, γ)
        case v => k(v, σ, γ)
    case ESLam(x, body) =>
      k(VSClo(x, body, ρ, ς), σ, γ)
    case ESApp(e, st) =>
      eval(e, ρ, ς, σ, { case (VSClo(x, body, ρf, ςf), σ1, γ1) =>
        eval(body, ρf, ςf + (x -> evalStVar(st, ς)), σ1, k, γ1)
      }, γ)
    case ELam(x, argTy, e, retTy) =>
      k(VClo(x, argTy, e, retTy, ρ, ς), σ, γ)
    case EBNLam(x, argTy, e, retTy) =>
      k(VBNClo(x, argTy, e, retTy, ρ, ς), σ, γ)
    case EApp(e1, e2, s) if evalExprStage(s, ς) == Sta =>
      eval(e1, ρ, ς, σ, {
        case (VBNClo(x, _, body, _, ρf, ςf), σ1, γ1) =>
          val v2 = VThunk(e2, ρ, ς)
          val l = σ1.size
          eval(body, ρf + (x -> l), ςf, σ1 + (l -> v2), k, γ1)
        case (VClo(x, _, body, _, ρf, ςf), σ1, γ1) =>
          eval(e2, ρ, ς, σ1, { case (v2, σ2, γ2) =>
            val l = σ2.size
            eval(body, ρf + (x -> l), ςf, σ2 + (l -> v2), k, γ2)
          }, γ1)
      }, γ)
    case EApp(e1, e2, s) if evalExprStage(s, ς) == Dyn =>
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
      // TODO: does meta-continuation need to observe current cache here?
      reify(e, ρ, ς, σ, { case (VCode(t), σ2) =>
        eval(t, Map(), Map(), σ2, k, γ)
      })
    case ELet(x, rhs, e) =>
      eval(rhs, ρ, ς, σ, (v, σ1, γ1) =>
        val l = σ1.size
        eval(e, ρ + (x -> l), ς, σ1 + (l -> v), k, γ1), γ)
    case ELetRec(f, rhs, e) =>
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
    case ECond(e1, e2, e3, s) if evalExprStage(s, ς) == Sta =>
      eval(e1, ρ, ς, σ, { case (VBool(b), σ1, γ1) =>
        if b then eval(e2, ρ, ς, σ1, k, γ1)
        else eval(e3, ρ, ς, σ1, k, γ1)
      }, γ)
    case ECond(e1, e2, e3, s) if evalExprStage(s, ς) == Dyn =>
      eval(e1, ρ, ς, σ, { case (VCode(x1), σ1, γ1) =>
        reify(e2, ρ, ς, σ1, { case (VCode(x2), σ2) =>
          reify(e3, ρ, ς, σ2, { case (VCode(x3), σ3) =>
            reflect(ECond1(x1, x2, x3), σ3, k, γ1)
          })
        })
      }, γ)
    case EBinOp(op, e1, e2, s) if evalExprStage(s, ς) == Sta =>
      eval(e1, ρ, ς, σ, { case (v1, σ1, γ1) =>
        eval(e2, ρ, ς, σ1, { case (v2, σ2, γ2) =>
          k(evalPrim(op, v1, v2), σ2, γ2)
        }, γ1)
      }, γ)
    case EBinOp(op, e1, e2, s) if evalExprStage(s, ς) == Dyn =>
      eval(e1, ρ, ς, σ, { case (VCode(x1), σ1, γ1) =>
        eval(e2, ρ, ς, σ1, { case (VCode(x2), σ2, γ2) =>
          reflect(EBinOp1(op, x1, x2), σ2, k, γ2)
        }, γ1)
      }, γ)
    case EUnaryOp(op, e, s) if evalExprStage(s, ς) == Sta =>
      eval(e, ρ, ς, σ, { case (v, σ1, γ1) =>
        k(evalPrimUnary(op, v), σ1, γ1)
      }, γ)
    case EUnaryOp(op, e, s) if evalExprStage(s, ς) == Dyn =>
      eval(e, ρ, ς, σ, { case (VCode(x), σ1, γ1) =>
        reflect(EUnaryOp1(op, x), σ1, k, γ1)
      }, γ)
    case EAlloc(e, s) if evalExprStage(s, ς) == Sta =>
      eval(e, ρ, ς, σ, { case (v, σ1, γ1) =>
        val l = σ1.size
        k(VLoc(l), σ1 + (l -> v), γ1)
      }, γ)
    case EAlloc(e, s) if evalExprStage(s, ς) == Dyn =>
      eval(e, ρ, ς, σ, { case (VCode(x), σ1, γ1) =>
        reflect(EAlloc1(x), σ1, k, γ1)
      }, γ)
    case EDeref(e, s) if evalExprStage(s, ς) == Sta =>
      eval(e, ρ, ς, σ, { case (VLoc(l), σ1, γ1) =>
        k(σ1(l), σ1, γ1)
      }, γ)
    case EDeref(e, s) if evalExprStage(s, ς) == Dyn =>
      eval(e, ρ, ς, σ, { case (VCode(x), σ1, γ1) =>
        reflect(EDeref1(x), σ1, k, γ1)
      }, γ)
    case EAssign(e1, e2, s) if evalExprStage(s, ς) == Sta =>
      eval(e1, ρ, ς, σ, { case (VLoc(l), σ1, γ1) =>
        eval(e2, ρ, ς, σ1, { case (v2, σ2, γ2) =>
          k(VUnit, σ2 + (l -> v2), γ2)
        }, γ1)
      }, γ)
    case EAssign(e1, e2, s) if evalExprStage(s, ς) == Dyn =>
      eval(e1, ρ, ς, σ, { case (VCode(x1), σ1, γ1) =>
        eval(e2, ρ, ς, σ1, { case (VCode(x2), σ2, γ2) =>
          reflect(EAssign1(x1, x2), σ2, k, γ2)
        }, γ1)
      }, γ)
    case EAscribe(e, _) => eval(e, ρ, ς, σ, k, γ)
    case EFix(f, e, s) if evalExprStage(s, ς) == Sta =>
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
    case EFix(f, e, s) if evalExprStage(s, ς) == Dyn =>
      val l = σ.size
      val ρ1 = ρ + (f -> l)
      val g = fresh("f")
      val σ1 = σ + (l -> VCode(EVar(g)))
      reify(e, ρ1, ς, σ1, { case (VCode(x), σ2) =>
        reflect(EFix(g, x, Some(Sta)), σ2, k, γ)
      })
    // Experimental features below:
    case EIsApp(e) => eval(e, ρ, ς, σ, isApp(k), γ)
    case ECBNApp(e1, e2) =>
      eval(e1, ρ, ς, σ, { case (VClo(x, _, body, _, ρf, ςf), σ1, γ1) =>
        val v2 = VThunk(e2, ρ, ς)
        val l = σ1.size
        eval(body, ρf + (x -> l), ςf, σ1 + (l -> v2), k, γ1)
      }, γ)

def eval(e: Expr): (Value, Store) =
  clear
  eval(e, Map(), Map(), Map(), (x, σ, γ) => γ(x, σ), (x, σ) => (x, σ))(using BiMap())
