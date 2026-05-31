// Object-code optimizations:
//   Section 5  — Reflect combinators & constant propagation (reflectAtom/reflectDefault/reflect)
//   Section 5  — Code cache for tracking inserted bindings (Cache / BiMap)
//   Section 6  — Common sub-expression elimination (reflectCse / CachedExpr)
//   Section 7  — Constant folding (reflectSimp / StaticConst)
//   Section 8  — Dead-code elimination (reflectDce)
//   Section 9  — Partially-static data (reflectPS / evalPS / Algebra.scala)
//   Section 10 — Inlining with renormalization (reflectInline / StaticLam / renormalize)
//   Section 11 — Code motion / λ-hoisting (hoist / hoistable / reflectLam)
//   Section 12 — Extensions: mutable refs, rec functions, by-name, intensional analysis

package instar.twocpsopt

import instar.syntax.*
import instar.Counter.*
import instar.BiMap
import instar.algebra.*
import instar.algebra.{freeRingCode, given}
import collection.mutable.HashSet

import Stage.*
import Expr.*
import Value.*

type Store = Map[Loc, Value]
type Cache = BiMap[Expr, String]
type Cont = (Value, Store, MCont) => Cache ?=> (Value, Store)
type MCont = (Value, Store) => (Value, Store)

type ⇀[A, B] = PartialFunction[A, B]

object Opt:
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

// Section 5: default fallback — let-insert a fresh variable and record it in the cache
def reflectDefault(σ: Store, k: Cont, γ: MCont)(using c: Cache): Expr ⇀ (Value, Store) =
  case e =>
    val x = fresh()
    k(VCode(EVar(x)), σ, {
      case (VCode(body), σ1) =>
        γ(VCode(ELet(x, e, body)), σ1)
    })(using c + (e -> x))

// Section 5: Pass through atomic expressions without let-insertion (constant propagation)
def reflectAtom(σ: Store, k: Cont, γ: MCont)(using c: Cache): Expr ⇀ (Value, Store) =
  case EUnit => k(VCode(EUnit), σ, γ)
  case ENum(i) => k(VCode(ENum(i)), σ, γ)
  case EBool(b) => k(VCode(EBool(b)), σ, γ)

// Section 6: reuse a previously generated variable for the same pure expression
object CachedExpr:
  def unapply(e: Expr)(using c: Cache): Option[EVar] =
    if (e.isPure && c.contains(e)) Some(EVar(c(e)))
    else None

def reflectCse(σ: Store, k: Cont, γ: MCont)(using c: Cache): Expr ⇀ (Value, Store) =
  case CachedExpr(x) if Opt("cse") =>
    k(VCode(x), σ, γ)

// Section 7: evaluate static binary operations at staging time
object StaticConst:
  def unapply(e: Expr)(using c: Cache): Option[Value] =
    e match
      case ENum(i) => Some(VNum(i))
      case EBool(b) => Some(VBool(b))
      case EVar(x) if c.inv.contains(x) => StaticConst.unapply(c.inv(x))
      case _ => None

def reflectSimp(σ: Store, k: Cont, γ: MCont)(using c: Cache): Expr ⇀ (Value, Store) =
  case EBinOp(op, StaticConst(v1), StaticConst(v2), _) if Opt("rewriting") && !Opt("ps") =>
    evalPrim(op, v1, v2) match
      case VNum(i) => reflect(ENum(i), σ, k, γ)
      case VBool(b) => reflect(EBool(b), σ, k, γ)

// Section 8: skip let-insertion if the bound variable is unused in the body
def reflectDce(σ: Store, k: Cont, γ: MCont)(using c: Cache): Expr ⇀ (Value, Store) =
  case e if Opt("dce") && e.isPure =>
    val x = fresh()
    k(VCode(EVar(x)), σ, { case (VCode(body), σ1) =>
      if (!body.freeVar(x)) γ(VCode(body), σ1)
      else γ(VCode(ELet(x, e, body)), σ1)
    })(using c + (e -> x))

// Section 9: recognize ring operations (+/*) for partially-static simplification
object CachedRingExpr:
  val AddMulRingOps = Set("+", "*")

  def unapply(e: Expr)(using c: Cache): Option[(String, Expr, Expr)] =
    e match
      case EBinOp(op, e1, e2, _) if AddMulRingOps(op) => Some((op, e1, e2))
      case EVar(x) if c.inv.contains(x) => unapply(c.inv(x))
      case _ => None

// Section 9: structural equivalence modulo let-normalization for PSD comparison
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

// Section 9: detect expressions whose PSD normalization differs from the original
object UnnormalizedExpr:
  def unapply(e: Expr)(using c: Cache): Option[Expr] =
    e match
      case CachedRingExpr(_, _, _) if Opt("ps") =>
        val normalized =
          cd(using freeRingCode, AddMulRingExprImpl, AddMulRingCoproductImpl)(evalPS(e))
        if e.equivalent(normalized) then None else Some(e)
      case _ => None

// Section 9: reinterpret expression as algebraic operations over the coproduct
type NormalForm = AddMulRingCoproductImpl.Coprod

def sta(i: Int): NormalForm =
  AddMulRingCoproductImpl.inl(i)

def dyn(e: Expr)(using c: Cache): NormalForm = e match
  case EVar(x) => AddMulRingCoproductImpl.inr(freeRingCode.pvar(EVar(x)))
  case e => AddMulRingCoproductImpl.inr(freeRingCode.pvar(EVar(c(e))))

def evalPS(expr: Expr)(using c: Cache): NormalForm =
  expr match
    case EBinOp("+", e1, e2, _) => evalPS(e1) ⊕ evalPS(e2)
    case EBinOp("*", e1, e2, _) => evalPS(e1) ⊗ evalPS(e2)
    case EVar(x) if c.inv.contains(x) && c.inv(x).isPure => evalPS(c.inv(x))
    case ENum(i) => sta(i)
    case e => dyn(e)

def residualizePS(repr: NormalForm, σ: Store, k: Cont, γ: MCont)(using c: Cache): (Value, Store) =
  val code = cd(using freeRingCode, AddMulRingExprImpl, AddMulRingCoproductImpl)(repr)
  renormalize(code, σ, k, γ)

// Section 9: residualize the normalized PSD representation back into code
def reflectPS(σ: Store, k: Cont, γ: MCont)(using c: Cache): Expr ⇀ (Value, Store) =
  case UnnormalizedExpr(e) if Opt("ps") => residualizePS(evalPS(e), σ, k, γ)

// Section 10: recognize static lambda terms for β-inlining, either syntactically or via the cache
object StaticLam:
  def unapply(e: Expr)(using c: Cache): Option[ELam] =
    e match
      case e@ELam(_, _) => Some(e)
      case EVar(f) if c.inv.contains(f) => StaticLam.unapply(c.inv(f))
      case _ => None

// Section 10: renormalization — replay let-bindings through reflect to restore ANF after inlining
def renormalize(e: Expr, σ: Store, k: Cont, γ: MCont)(using c: Cache): (Value, Store) = e match
  case ELet(x, rhs, body) =>
    reflect(rhs, σ, { case (VCode(t), σ1, γ1) =>
      renormalize(body.subst(x, t), σ1, k, γ1)
    }, γ)
  case _ => k(VCode(e), σ, γ)

// Section 10: substitute argument into function body, then renormalize to restore ANF
def reflectInline(σ: Store, k: Cont, γ: MCont)(using c: Cache): Expr ⇀ (Value, Store) =
  case EApp(StaticLam(ELam(x, body)), arg, _) if Opt("fun-inline") =>
    renormalize(body.subst(x, arg), σ, k, γ)

// Section 10: statically choose a branch when the condition is constant
def reflectCondSimp(σ: Store, k: Cont, γ: MCont)(using c: Cache): Expr ⇀ (Value, Store) =
  case ECond(StaticConst(VBool(b)), e2, e3, _) if Opt("simp-cond") =>
    if b then renormalize(e2, σ, k, γ)
    else renormalize(e3, σ, k, γ)

// Section 11: check whether a binding is independent of previously scheduled code
def hoistable(e: Expr)(using c: Cache): Boolean =
  e.isPure && e.freeVar.intersect(c.allVals).isEmpty

// Section 11: partition let-bindings — hoistable ones go into the meta-continuation
def hoist(e: Expr, σ: Store, k: Cont, γ: MCont)(using c: Cache): (Value, Store) =
  e match
    case ELet(x, rhs, body) if hoistable(rhs) =>
      hoist(body, σ, k, { case (VCode(body1), σ1) =>
        γ(VCode(ELet(x, rhs, body1)), σ1)
      })(using c + (rhs -> x))
    case ELet(x, rhs, body) =>
      hoist(body, σ, { case (VCode(body1), σ1, γ1) =>
        k(VCode(ELet(x, rhs, body1)), σ1, γ1)
      }, γ)(using c + (rhs -> x))
    case _ => k(VCode(e), σ, γ)

// compose all reflect combinators in priority order, falling back to reflectDefault
def reflect(e: Expr, σ: Store, k: Cont, γ: MCont)(using c: Cache): (Value, Store) =
  val funs = List(
    reflectAtom,
    reflectInline,
    reflectSimp,
    reflectPS,
    reflectCondSimp,
    reflectCse,
    reflectDce,
  )
  funs.foldRight(reflectDefault(σ, k, γ)) { (f, acc) => f(σ, k, γ).orElse(acc) }(e)

def reify(e: Expr, ρ: Env, σ: Store, γ: MCont)(using c: Cache): (Value, Store) =
  eval(e, ρ, σ, (x, σ1, γ1) => γ1(x, σ1), γ)

def lift(k: Cont)(v: Value, σ: Store, γ: MCont)(using c: Cache): (Value, Store) = v match
  case VUnit => reflect(EUnit, σ, k, γ)
  case VNum(i) => reflect(ENum(i), σ, k, γ)
  case VBool(b) => reflect(EBool(b), σ, k, γ)
  case VLoc(l) => reflect(ELoc(l), σ, k, γ)
  case VClo(x, body, ρf) =>
    val l = σ.size
    val y = fresh()
    reify(body, ρf + (x -> l), σ + (l -> VCode(EVar(y))), {
      case (VCode(t), σ2) =>
        if (Opt("lam-hoist"))
          hoist(t, σ2, { case (VCode(t1), σ3, γ1) =>
            reflect(ELam(y, t1), σ3, (v, σ3, γ1) => γ1(v, σ3), γ1)
          }, { case (VCode(t1), σ3) =>
            renormalize(t1, σ3, k, γ)
          })(using BiMap((EVar(y) -> y)))
        else
          reflect(ELam(y, t), σ2, k, γ)
    })

def isApp(k: Cont)(v: Value, σ: Store, γ: MCont)(using c: Cache): (Value, Store) = v match
  case VCode(EVar(x)) =>
    c.inv(x) match
      case EApp(_, _, _) => k(VBool(true), σ, γ)
      case _ => k(VBool(false), σ, γ)
  case VCode(_) => k(VBool(false), σ, γ)

def eval(e: Expr, ρ: Env, σ: Store, k: Cont, γ: MCont)(using c: Cache): (Value, Store) =
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
        // Section 12: forcing a by-name thunk
        case VThunk(e, ρ) => eval(e, ρ, σ, k, γ)
        case v => k(v, σ, γ)
    case ELam(x, e) =>
      k(VClo(x, e, ρ), σ, γ)
    // Section 12: by-name lambda
    case EBNLam(x, e) =>
      k(VBNClo(x, e, ρ), σ, γ)
    case EApp(e1, e2, Sta) =>
      eval(e1, ρ, σ, {
        // Section 12: by-name application — package argument as a thunk
        case (VBNClo(x, body, ρf), σ1, γ1) =>
          val v2 = VThunk(e2, ρ)
          val l = σ1.size
          eval(body, ρf + (x -> l), σ1 + (l -> v2), k, γ1)
        case (VClo(x, body, ρf), σ1, γ1) =>
          eval(e2, ρ, σ1, { case (v2, σ2, γ2) =>
            val l = σ2.size
            eval(body, ρf + (x -> l), σ2 + (l -> v2), k, γ2)
          }, γ1)
      }, γ)
    case EApp(e1, e2, Dyn) =>
      eval(e1, ρ, σ, { case (VCode(x1), σ1, γ1) =>
        eval(e2, ρ, σ1, { case (VCode(x2), σ2, γ2) =>
          reflect(EApp1(x1, x2), σ2, k, γ2)
        }, γ1)
      }, γ)
    case ELift(e) =>
      eval(e, ρ, σ, lift(k), γ)
    case ERun(e) =>
      reify(e, ρ, σ, { case (VCode(t), σ2) =>
        eval(t, Map(), σ2, k, γ)
      })
    case ELet(x, rhs, e) =>
      eval(rhs, ρ, σ, (v, σ1, γ1) =>
        val l = σ1.size
        eval(e, ρ + (x -> l), σ1 + (l -> v), k, γ1), γ)
    case ECond(e1, e2, e3, Sta) =>
      eval(e1, ρ, σ, { case (VBool(b), σ1, γ1) =>
        if b then eval(e2, ρ, σ1, k, γ1)
        else eval(e3, ρ, σ1, k, γ1)
      }, γ)
    case ECond(e1, e2, e3, Dyn) =>
      eval(e1, ρ, σ, { case (VCode(x1), σ1, γ1) =>
        reify(e2, ρ, σ1, { case (VCode(x2), σ2) =>
          reify(e3, ρ, σ2, { case (VCode(x3), σ3) =>
            reflect(ECond1(x1, x2, x3), σ3, k, γ1)
          })
        })
      }, γ)
    case EBinOp(op, e1, e2, Sta) =>
      eval(e1, ρ, σ, { case (v1, σ1, γ1) =>
        eval(e2, ρ, σ1, { case (v2, σ2, γ2) =>
          k(evalPrim(op, v1, v2), σ2, γ2)
        }, γ1)
      }, γ)
    case EBinOp(op, e1, e2, Dyn) =>
      eval(e1, ρ, σ, { case (VCode(x1), σ1, γ1) =>
        eval(e2, ρ, σ1, { case (VCode(x2), σ2, γ2) =>
          reflect(EBinOp1(op, x1, x2), σ2, k, γ2)
        }, γ1)
      }, γ)
    case EUnaryOp(op, e, Sta) =>
      eval(e, ρ, σ, { case (v, σ1, γ1) =>
        k(evalPrimUnary(op, v), σ1, γ1)
      }, γ)
    case EUnaryOp(op, e, Dyn) =>
      eval(e, ρ, σ, { case (VCode(x), σ1, γ1) =>
        reflect(EUnaryOp1(op, x), σ1, k, γ1)
      }, γ)
    // Section 12: mutable references — allocate, dereference, assign
    case EAlloc(e, Sta) =>
      eval(e, ρ, σ, { case (v, σ1, γ1) =>
        val l = σ1.size
        k(VLoc(l), σ1 + (l -> v), γ1)
      }, γ)
    case EAlloc(e, Dyn) =>
      eval(e, ρ, σ, { case (VCode(x), σ1, γ1) =>
        reflect(EAlloc1(x), σ1, k, γ1)
      }, γ)
    case EDeref(e, Sta) =>
      eval(e, ρ, σ, { case (VLoc(l), σ1, γ1) =>
        k(σ1(l), σ1, γ1)
      }, γ)
    case EDeref(e, Dyn) =>
      eval(e, ρ, σ, { case (VCode(x), σ1, γ1) =>
        reflect(EDeref1(x), σ1, k, γ1)
      }, γ)
    case EAssign(e1, e2, Sta) =>
      eval(e1, ρ, σ, { case (VLoc(l), σ1, γ1) =>
        eval(e2, ρ, σ1, { case (v2, σ2, γ2) =>
          k(VUnit, σ2 + (l -> v2), γ2)
        }, γ1)
      }, γ)
    case EAssign(e1, e2, Dyn) =>
      eval(e1, ρ, σ, { case (VCode(x1), σ1, γ1) =>
        eval(e2, ρ, σ1, { case (VCode(x2), σ2, γ2) =>
          reflect(EAssign1(x1, x2), σ2, k, γ2)
        }, γ1)
      }, γ)
    // Section 12: letrec — allocate a store location, then tie the knot
    case ELetRec(f, rhs, e) =>
      eval(rhs, ρ, σ, {
        case (VClo(x, body, ρf), σ1, γ1) =>
          val l = σ1.size
          val ρf1 = ρf + (f -> l)
          val v = VClo(x, body, ρf1)
          eval(e, ρ + (f -> l), σ1 + (l -> v), k, γ1)
      }, γ)
    // Section 12: or alternatively, fixed-point combinator for recursive functions
    case EFix(f, e, Sta) =>
      eval(e, ρ, σ, {
        case (VClo(x, body, ρf), σ1, γ1) =>
          val l = σ1.size
          val v = VClo(x, body, ρf + (f -> l))
          k(v, σ1 + (l -> v), γ1)
      }, γ)
    case EFix(f, e, Dyn) =>
      val l = σ.size
      val ρ1 = ρ + (f -> l)
      val g = fresh("f")
      val σ1 = σ + (l -> VCode(EVar(g)))
      reify(e, ρ1, σ1, { case (VCode(x), σ2) =>
        reflect(EFix(g, x, Sta), σ2, k, γ)
      })
    // Section 12: intensional code inspection — test if code is an application
    case EIsApp(e) => eval(e, ρ, σ, isApp(k), γ)
    // Section 12: call-by-name application
    case ECBNApp(e1, e2) =>
      eval(e1, ρ, σ, { case (VClo(x, body, ρf), σ1, γ1) =>
        val v2 = VThunk(e2, ρ)
        val l = σ1.size
        eval(body, ρf + (x -> l), σ1 + (l -> v2), k, γ1)
      }, γ)

def eval(e: Expr): (Value, Store) =
  clear
  eval(e, Map(), Map(), (x, σ, γ) => γ(x, σ), (x, σ) => (x, σ))(using BiMap())
