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
import instar.algebra.*
import instar.algebra.{freeRingCode, given}
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
  def erase: Option[Type] = t.map(_.erase)

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

object CachedRingExpr:
  val AddMulRingOps = Set("+", "*")

  def unapply(e: Expr)(using c: Cache): Option[(String, Expr, Expr)] =
    e match
      case EBinOp(op, e1, e2, _) if AddMulRingOps(op) => Some((op, e1, e2))
      case EVar(x) if c.inv.contains(x) => unapply(c.inv(x))
      case _ => None

// let x3 = x1 + x3 in let x4 = x3 * x3 is equivalent to
// (x1 + x3) * (x1 + x3)
extension (e1: Expr)
  def equivalent(e2: Expr)(using c: Cache): Boolean =
    (e1, e2) match
      case (ELet(x1, e11, e12), _) => e12.equivalent(e2)(using c + (e11 -> x1))
      case (_, ELet(x2, e21, e22)) => e1.equivalent(e22)(using c + (e21 -> x2))
      case (EVar(x1), _) if c.inv.contains(x1) => c.inv(x1).equivalent(e2)
      case (_, EVar(x2)) if c.inv.contains(x2) => e1.equivalent(c.inv(x2))
      case (EBinOp(op1, e11, e12, _), EBinOp(op2, e21, e22, _)) =>
        op1 == op2 && e11.equivalent(e21) && e12.equivalent(e22)
      case _ => e1 == e2

object UnnormalizedExpr:
  def unapply(e: Expr)(using c: Cache): Option[Expr] =
    e match
      case CachedRingExpr(_, _, _) if Opt("ps") =>
        val normalized =
          cd(using freeRingCode, AddMulRingExprImpl, AddMulRingCoproductImpl)(evalPS(e))
        if e.equivalent(normalized) then None else Some(e)
      case _ => None

type NormalForm = AddMulRingCoproductImpl.Coprod

def dyn(x: String): NormalForm =
  AddMulRingCoproductImpl.inr(freeRingCode.pvar(EVar(x)))

def evalPS(expr: Expr)(using c: Cache): NormalForm =
  expr match
    case CachedRingExpr("+", e1, e2) => evalPS(e1) ⊕ evalPS(e2)
    case CachedRingExpr("*", e1, e2) => evalPS(e1) ⊗ evalPS(e2)
    case ENum(i) => sta[Ring, Int](i)
    case EVar(x) => dyn(x)

def residualizePS(repr: NormalForm, σ: Store, k: Cont, γ: MCont)(using c: Cache): (Value, Store) =
  val code = cd(using freeRingCode, AddMulRingExprImpl, AddMulRingCoproductImpl)(repr)
  // println(s"residualizePS: residualizing $code with repr = $repr")
  renormalize(code, σ, k, γ)

def reflectPS(σ: Store, k: Cont, γ: MCont)(using c: Cache): Expr ⇀ (Value, Store) =
  case UnnormalizedExpr(e) if Opt("ps") => residualizePS(evalPS(e), σ, k, γ)

// A list of optimization functions. We apply each of them, until one of them can handle the current expression.
// When the result is different from the input, we apply the result.
def reflect(e: Expr, σ: Store, k: Cont, γ: MCont)(using c: Cache): (Value, Store) =
  val funs = List(
    reflectAtom,
    reflectLam,
    reflectInline,
    reflectSimp, // There should be a reflectPS that replaces reflectSimp
    reflectPS,
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
  case code @ VCode(_) => k(code, σ, γ)
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
    case ESLam(s, body, _) =>
      k(VSClo(s, body, ρ, ς), σ, γ)
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
    case ELetRec(f, rhs, e, st) if evalExprStage(st, ς) == Sta =>
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
    case ELetRec(f, rhs, e, st) if evalExprStage(st, ς) == Dyn =>
      val name = fresh()
      val l = σ.size
      val recursiveEnv = ρ + (f -> l)
      reify(rhs, recursiveEnv, ς, σ + (l -> VCode(EVar(name))), {
        case (VCode(code), σ1) =>
          eval(e, recursiveEnv, ς, σ1, k, { case (VCode(body), σ2) =>
            γ(VCode(ELetRec(name, code, body, Some(Sta))), σ2)
          })
      })
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
