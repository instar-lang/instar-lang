package spmp.eff.opt

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

import spmp.Counter.*
import spmp.BiMap
import collection.mutable.{HashSet, HashMap}
import spmp.eff.opt.Opt.opt
import scala.annotation.init
import scala.Conversion

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
  var normalized: Boolean = false
  def withNormalized: Expr = { normalized = true; this }
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
  case EPrimOp(op: String, rands: List[Expr], st: Stage)
  case EAlloc(e: Expr, st: Stage)
  case EDeref(e: Expr, st: Stage)
  case EAssign(e1: Expr, e2: Expr, st: Stage)
  case EAscribe(e: Expr, asTy: Type)
  case EFix(f: String, e: Expr, st: Stage)
  case ELoc(l: Loc)
  // Experimental:
  // extend the language to allow programmers to inspect code values
  case EIsApp(e: Expr)
  // TODO: what's the general pattern matching form on Code?

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
      case ESLam(_, _) | ELam(_, _, _, _) => true
      case EBinOp(_, _, _, _) | EUnaryOp(_, _, _) => true
      case ESApp(_, _) | EApp(_, _, _) => false
      case ELift(t, _) => false
      case EAlloc(_, _) | EDeref(_, _) | EAssign(_, _, _) => false
      case ERun(t) => t.isPure
      case ELet(_, rhs, body) => rhs.isPure && body.isPure
      case ELetRec(_, _, rhs, body) => rhs.isPure && body.isPure
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
      case ELift(t, _) => t.freeVar
      case ERun(t) => t.freeVar
      case ELet(x, rhs, body) => rhs.freeVar ++ (body.freeVar - x)
      case ELetRec(f, _, rhs, body) => (rhs.freeVar - f) ++ (body.freeVar - f)
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
      case ELetRec(f, fnty, rhs, body) =>
        ELetRec(f, fnty, rhs.subst(from, to), body.subst(from, to))
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
  // Variables are also an atom. We don't need this case for other evaluators since they maintain an invariant: never reflect variables.
  // After adding partially static optimizations, we may reflect variables. We don't need to worry about the variable capture here since
  // all the generated variables are distinct.
  case EVar(name) => k(VCode(EVar(name)), σ, γ)


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

object VNumAddMonoid extends Monoid[VNum]:
  def empty: VNum = VNum(0)
  extension (x: VNum)
    def ⊗(rhs: VNum): VNum = VNum(x.i + rhs.i)

object VNumMulMonoid extends Monoid[VNum]:
  def empty: VNum = VNum(1)
  extension (x: VNum)
    def ⊗(rhs: VNum): VNum = VNum(x.i * rhs.i)

given [T]: Free[Monoid, T] with
  case class FreeA(l: List[T])

  given af: Monoid[FreeA] with
    def empty: FreeA = FreeA(List())
    extension (x: FreeA)
      def ⊗(rhs: FreeA): FreeA = FreeA(x.l ++ rhs.l)

  def pvar(x: T): FreeA = FreeA(List(x))

  def pbind[C: Monoid](freeA: FreeA)(f: T => C): C =
    freeA.l.map(f).reduce(_ ⊗_)

given [X, T](using r: Ring[T]): Ring[Multinomial[X, T]] = new MultinomialRing[X, T]

given Ring[Int] with
  def zero: Int = 0
  def one: Int = 1

  extension (x: Int)
    def +(rhs: Int): Int = x + rhs
    def *(rhs: Int): Int = x * rhs

// Let Code be a monomorphic type Expr
type Code = EVar

given Ring[VNum] with
  def zero: VNum = VNum(0)
  def one: VNum = VNum(1)

  extension (x: VNum)
    def +(rhs: VNum): VNum = VNum(x.i + rhs.i)
    def *(rhs: VNum): VNum = VNum(x.i * rhs.i)

given Conversion[VNum, Expr] with
  def apply(v: VNum): Expr = ENum1(v.i)

val freeMonoidCode: Free[Monoid, Code] = new FreeCMonoid[Code]

// TODO: can a type have multiple implementations of the same algebra?
val freeRingCode: FreeRing[Code] = new FreeRing[Code]

object AddMulRingCoproductImpl extends Coproduct[Ring, VNum, freeRingCode.FreeA]:
  val inst: Coproduct[Ring, VNum, freeRingCode.FreeA] =
    coproductFromFreeRing[VNum, Code](using summon[Ring[VNum]])(using freeRingCode)

  type Coprod = inst.Coprod
  given ac: Ring[Coprod] = inst.ac

  override def inl(a: VNum): Coprod = inst.inl(a)

  override def inr(b: freeRingCode.FreeA): Coprod = inst.inr(b)

  override def eva[C: Ring](fa: VNum => C)(fb: freeRingCode.FreeA => C)(co: Coprod): C =
    inst.eva(fa)(fb)(co)

object AddCMonoidCoproductImpl
  extends Coproduct[Monoid, VNum, freeMonoidCode.FreeA](using VNumAddMonoid, freeMonoidCode.af):
  val inst: Coproduct[Monoid, VNum, freeMonoidCode.FreeA] =
    coproductFromFreeMonoid[VNum, Code](using VNumAddMonoid, freeMonoidCode)

  type Coprod = inst.Coprod
  given ac: Monoid[Coprod] = inst.ac

  override def inl(a: VNum): Coprod = inst.inl(a)
  override def inr(b: freeMonoidCode.FreeA): Coprod = inst.inr(b)
  override def eva[C: Monoid](fa: VNum => C)(fb: freeMonoidCode.FreeA => C)(co: Coprod): C =
    inst.eva(fa)(fb)(co)

object MulCMonoidCoproductImpl
  extends Coproduct[Monoid, VNum, freeMonoidCode.FreeA](using VNumMulMonoid, freeMonoidCode.af):
  val inst: Coproduct[Monoid, VNum, freeMonoidCode.FreeA] =
    coproductFromFreeMonoid[VNum, Code](using VNumMulMonoid, freeMonoidCode)

  type Coprod = inst.Coprod
  given ac: Monoid[Coprod] = inst.ac

  override def inl(a: VNum): Coprod = inst.inl(a)
  override def inr(b: freeMonoidCode.FreeA): Coprod = inst.inr(b)
  override def eva[C: Monoid](fa: VNum => C)(fb: freeMonoidCode.FreeA => C)(co: Coprod): C =
    inst.eva(fa)(fb)(co)

trait TopCoproduct:
  def +(rhs: TopCoproduct): TopCoproduct
  def *(rhs: TopCoproduct): TopCoproduct
  def -(rhs: TopCoproduct): TopCoproduct
  def /(rhs: TopCoproduct): TopCoproduct
  def code: Expr

object AddMulRingExprImpl extends Ring[Expr]:
  def zero: Expr = ENum(0).withNormalized
  def one: Expr = ENum(1).withNormalized

  extension (x: Expr)
    def +(rhs: Expr): Expr =
      if (x == zero) rhs.withNormalized
      else if (rhs == zero) x.withNormalized
      else EBinOp("+", x, rhs, Sta).withNormalized

    def *(rhs: Expr): Expr =
      if (x == one) rhs.withNormalized
      else if (rhs == one) x.withNormalized
      else if (x == zero || rhs == zero) zero
      else EBinOp("*", x, rhs, Sta).withNormalized

object AddCMonoidExprImpl extends Monoid[Expr]:
  def empty: Expr = ENum(0).withNormalized

  extension (x: Expr)
    def ⊗(rhs: Expr): Expr =
      if (x == empty) rhs.withNormalized
      else if (rhs == empty) x.withNormalized
      else EBinOp("+", x, rhs, Sta).withNormalized

object MulCMonoidExprImpl extends Monoid[Expr]:
  def empty: Expr = ENum(1).withNormalized

  extension (x: Expr)
    def ⊗(rhs: Expr): Expr =
      if (x == empty) rhs.withNormalized
      else if (rhs == empty) x.withNormalized
      else EBinOp("*", x, rhs, Sta).withNormalized

def liftAddCToRing(value: AddCMonoidCoproductImpl.Coprod): AddMulRingCoproductImpl.Coprod =
  given Ring[AddMulRingCoproductImpl.Coprod] = AddMulRingCoproductImpl.ac
  given Monoid[AddMulRingCoproductImpl.Coprod] with
    def empty: AddMulRingCoproductImpl.Coprod = summon[Ring[AddMulRingCoproductImpl.Coprod]].zero
    extension (x: AddMulRingCoproductImpl.Coprod)
      def ⊗(rhs: AddMulRingCoproductImpl.Coprod): AddMulRingCoproductImpl.Coprod =
        x + rhs

  val elim1 = (v: VNum) => AddMulRingCoproductImpl.inl(v)
  val elim2 = (freeA: freeMonoidCode.FreeA) =>
    freeMonoidCode.pbind(freeA) { (code: Code) =>
      AddMulRingCoproductImpl.inr(freeRingCode.pvar(code))
    }
  AddCMonoidCoproductImpl.eva[AddMulRingCoproductImpl.Coprod](elim1)(elim2)(value)

given addCMonoidToRingCoproduct: Conversion[AddCMonoidCoproductImpl.Coprod, AddMulRingCoproductImpl.Coprod] with
  def apply(value: AddCMonoidCoproductImpl.Coprod): AddMulRingCoproductImpl.Coprod =
    liftAddCToRing(value)

def liftMulCToRing(value: MulCMonoidCoproductImpl.Coprod): AddMulRingCoproductImpl.Coprod =
  given Ring[AddMulRingCoproductImpl.Coprod] = AddMulRingCoproductImpl.ac
  given Monoid[AddMulRingCoproductImpl.Coprod] with
    def empty: AddMulRingCoproductImpl.Coprod = summon[Ring[AddMulRingCoproductImpl.Coprod]].one
    extension (x: AddMulRingCoproductImpl.Coprod)
      def ⊗(rhs: AddMulRingCoproductImpl.Coprod): AddMulRingCoproductImpl.Coprod =
        x * rhs

  val elim1 =(v: VNum) => AddMulRingCoproductImpl.inl(v)
  val elim2 = (freeA: freeMonoidCode.FreeA) =>
    freeMonoidCode.pbind(freeA) { (code: Code) =>
      AddMulRingCoproductImpl.inr(freeRingCode.pvar(code))
    }
  MulCMonoidCoproductImpl.eva[AddMulRingCoproductImpl.Coprod](elim1)(elim2)(value)

given mulCMonoidToRingCoproduct: Conversion[MulCMonoidCoproductImpl.Coprod, AddMulRingCoproductImpl.Coprod] with
  def apply(value: MulCMonoidCoproductImpl.Coprod): AddMulRingCoproductImpl.Coprod =
    liftMulCToRing(value)

class AddMulRingRepr(val ringRepr: AddMulRingCoproductImpl.Coprod) extends TopCoproduct:
  override def +(rhs: TopCoproduct): TopCoproduct = rhs match
    case rhsRing: AddMulRingRepr => new AddMulRingRepr(ringRepr + rhsRing.ringRepr)
    case DynRepr(EVar(name)) =>
      given Ring[AddMulRingCoproductImpl.Coprod] = AddMulRingCoproductImpl.ac
      val rhs = AddMulRingCoproductImpl.inr(freeRingCode.pvar(EVar(name)))
      new AddMulRingRepr(ringRepr + rhs)
    case DynRepr(ENum(i)) =>
      given Ring[AddMulRingCoproductImpl.Coprod] = AddMulRingCoproductImpl.ac
      val rhs = AddMulRingCoproductImpl.inl(VNum(i))
      new AddMulRingRepr(ringRepr + rhs)
    case _ => new DynRepr(EBinOp("+", code, rhs.code, Sta))

  override def *(rhs: TopCoproduct): TopCoproduct = rhs match
    case rhsRing: AddMulRingRepr => new AddMulRingRepr(ringRepr * rhsRing.ringRepr)
    case DynRepr(EVar(name)) =>
      given Ring[AddMulRingCoproductImpl.Coprod] = AddMulRingCoproductImpl.ac
      val rhsRing = AddMulRingCoproductImpl.inr(freeRingCode.pvar(EVar(name)))
      new AddMulRingRepr(ringRepr * rhsRing)
    case DynRepr(ENum(i)) =>
      given Ring[AddMulRingCoproductImpl.Coprod] = AddMulRingCoproductImpl.ac
      val rhsRing = AddMulRingCoproductImpl.inl(VNum(i))
      new AddMulRingRepr(ringRepr * rhsRing)
    case _ => new DynRepr(EBinOp("*", code, rhs.code, Sta))

  override def -(rhs: TopCoproduct): TopCoproduct =
    new DynRepr(EBinOp("-", code, rhs.code, Sta))

  override def /(rhs: TopCoproduct): TopCoproduct =
    new DynRepr(EBinOp("/", code, rhs.code, Sta))

  override def code: Expr =
    cd(using freeRingCode, AddMulRingExprImpl, AddMulRingCoproductImpl)(ringRepr)

class AddCMonoidRepr(val cmonoidRepr: AddCMonoidCoproductImpl.Coprod) extends AddMulRingRepr(cmonoidRepr):
  given Monoid[AddCMonoidCoproductImpl.Coprod] = AddCMonoidCoproductImpl.ac
  override def +(rhs: TopCoproduct): TopCoproduct = rhs match
    case rhsAdd: AddCMonoidRepr =>
      new AddCMonoidRepr(cmonoidRepr ⊗ rhsAdd.cmonoidRepr)
    case DynRepr(EVar(name)) =>
      val rhs = AddCMonoidCoproductImpl.inr(freeMonoidCode.pvar(EVar(name)))
      new AddCMonoidRepr(cmonoidRepr ⊗ rhs)
    case DynRepr(ENum(i)) =>
      val rhs = AddCMonoidCoproductImpl.inl(VNum(i))
      new AddCMonoidRepr(cmonoidRepr ⊗ rhs)
    case _ => super.+(rhs)

  override def code: Expr =
    given Monoid[VNum] = VNumAddMonoid
    cd(using freeMonoidCode, AddCMonoidExprImpl, AddCMonoidCoproductImpl)(cmonoidRepr)

class MulCMonoidRepr(val cmonoidRepr: MulCMonoidCoproductImpl.Coprod) extends AddMulRingRepr(cmonoidRepr):
  given Monoid[MulCMonoidCoproductImpl.Coprod] = MulCMonoidCoproductImpl.ac
  override def *(rhs: TopCoproduct): TopCoproduct = rhs match
    case rhsMul: MulCMonoidRepr =>
      new MulCMonoidRepr(cmonoidRepr ⊗ rhsMul.cmonoidRepr)
    case DynRepr(EVar(name)) =>
      val rhs = MulCMonoidCoproductImpl.inr(freeMonoidCode.pvar(EVar(name)))
      new MulCMonoidRepr(cmonoidRepr ⊗ rhs)
    case _ => super.*(rhs)

  override def code: Expr =
    given Monoid[VNum] = VNumMulMonoid
    cd(using freeMonoidCode, MulCMonoidExprImpl, MulCMonoidCoproductImpl)(cmonoidRepr)

case class DynRepr(val expr: Expr) extends TopCoproduct:
  override def +(rhs: TopCoproduct): TopCoproduct = (expr, rhs) match
    case (ENum(i), rhsDyn: DynRepr) =>
      rhsDyn.expr match
        case ENum(j) =>
          given Monoid[AddCMonoidCoproductImpl.Coprod] = AddCMonoidCoproductImpl.ac
          new AddCMonoidRepr(AddCMonoidCoproductImpl.inl(VNum(i)) ⊗ AddCMonoidCoproductImpl.inl(VNum(j)))
        case EVar(rhsName) =>
          val lhs = AddCMonoidCoproductImpl.inl(VNum(i))
          val rhsC = AddCMonoidCoproductImpl.inr(freeMonoidCode.pvar(EVar(rhsName)))
          new AddCMonoidRepr(lhs ⊗ rhsC)
        case _ =>
          new DynRepr(EBinOp("+", expr, rhsDyn.code, Sta))
    case (ENum(i), rhsAdd: AddCMonoidRepr) =>
      val lhs = AddCMonoidCoproductImpl.inl(VNum(i))
      new AddCMonoidRepr(lhs ⊗ rhsAdd.cmonoidRepr)
    case (EVar(name), rhsDyn: DynRepr) =>
      rhsDyn.expr match
        case ENum(i) =>
          val lhs = AddCMonoidCoproductImpl.inr(freeMonoidCode.pvar(EVar(name)))
          val rhsC = AddCMonoidCoproductImpl.inl(VNum(i))
          new AddCMonoidRepr(lhs ⊗ rhsC)
        case EVar(rhsName) =>
          val lhs = AddCMonoidCoproductImpl.inr(freeMonoidCode.pvar(EVar(name)))
          val rhsC = AddCMonoidCoproductImpl.inr(freeMonoidCode.pvar(EVar(rhsName)))
          new AddCMonoidRepr(lhs ⊗ rhsC)
        case _ =>
          new DynRepr(EBinOp("+", expr, rhsDyn.code, Sta))
    case (EVar(name), rhsAdd: AddCMonoidRepr) =>
      given Monoid[AddCMonoidCoproductImpl.Coprod] = AddCMonoidCoproductImpl.ac
      val lhs = AddCMonoidCoproductImpl.inr(freeMonoidCode.pvar(EVar(name)))
      new AddCMonoidRepr(lhs ⊗ rhsAdd.cmonoidRepr)
    case (EVar(name), rhsRing: AddMulRingRepr) =>
      given Ring[AddMulRingCoproductImpl.Coprod] = AddMulRingCoproductImpl.ac
      val lhs = AddMulRingCoproductImpl.inr(freeRingCode.pvar(EVar(name)))
      new AddMulRingRepr(lhs + rhsRing.ringRepr)
    case _ =>
      new DynRepr(EBinOp("+", code, rhs.code, Sta))

  override def *(rhs: TopCoproduct): TopCoproduct = (expr, rhs) match
    case (ENum(i), rhsDyn: DynRepr) =>
      rhsDyn.expr match
        case ENum(j) =>
          given Monoid[MulCMonoidCoproductImpl.Coprod] = MulCMonoidCoproductImpl.ac
          new MulCMonoidRepr(MulCMonoidCoproductImpl.inl(VNum(i)) ⊗ MulCMonoidCoproductImpl.inl(VNum(j)))
        case EVar(rhsName) =>
          val lhs = MulCMonoidCoproductImpl.inl(VNum(i))
          val rhsC = MulCMonoidCoproductImpl.inr(freeMonoidCode.pvar(EVar(rhsName)))
          new MulCMonoidRepr(lhs ⊗ rhsC)
        case _ =>
          new DynRepr(EBinOp("*", expr, rhsDyn.code, Sta))
    case (ENum(i), rhsMul: MulCMonoidRepr) =>
      given Monoid[MulCMonoidCoproductImpl.Coprod] = MulCMonoidCoproductImpl.ac
      val lhs = MulCMonoidCoproductImpl.inl(VNum(i))
      new MulCMonoidRepr(lhs ⊗ rhsMul.cmonoidRepr)
    case (ENum(i), rhsRing: AddMulRingRepr) =>
      given Ring[AddMulRingCoproductImpl.Coprod] = AddMulRingCoproductImpl.ac
      val lhs = AddMulRingCoproductImpl.inl(VNum(i))
      new AddMulRingRepr(lhs * rhsRing.ringRepr)
    case (EVar(name), rhsDyn: DynRepr) =>
      rhsDyn.expr match
        case ENum(i) =>
          val lhs = MulCMonoidCoproductImpl.inr(freeMonoidCode.pvar(EVar(name)))
          val rhsC = MulCMonoidCoproductImpl.inl(VNum(i))
          new MulCMonoidRepr(lhs ⊗ rhsC)
        case EVar(rhsName) =>
          val lhs = MulCMonoidCoproductImpl.inr(freeMonoidCode.pvar(EVar(name)))
          val rhsC = MulCMonoidCoproductImpl.inr(freeMonoidCode.pvar(EVar(rhsName)))
          new MulCMonoidRepr(lhs ⊗ rhsC)
        case _ =>
          new DynRepr(EBinOp("*", expr, rhsDyn.code, Sta))
    case (EVar(name), rhsMul: MulCMonoidRepr) =>
      given Monoid[MulCMonoidCoproductImpl.Coprod] = MulCMonoidCoproductImpl.ac
      val lhs = MulCMonoidCoproductImpl.inr(freeMonoidCode.pvar(EVar(name)))
      new MulCMonoidRepr(lhs ⊗ rhsMul.cmonoidRepr)
    case (EVar(name), rhsRing: AddMulRingRepr) =>
      given Ring[AddMulRingCoproductImpl.Coprod] = AddMulRingCoproductImpl.ac
      val lhs = AddMulRingCoproductImpl.inr(freeRingCode.pvar(EVar(name)))
      new AddMulRingRepr(lhs * rhsRing.ringRepr)
    case _ =>
      new DynRepr(EBinOp("*", code, rhs.code, Sta))

  override def -(rhs: TopCoproduct): TopCoproduct = (expr, rhs) match
    case (ENum(i), rhsDyn: DynRepr) =>
      rhsDyn.expr match
        case ENum(j) => new DynRepr(ENum(i - j).withNormalized)
        case _ => new DynRepr(EBinOp("-", expr, rhsDyn.code, Sta))
    case _ =>
      new DynRepr(EBinOp("-", code, rhs.code, Sta))

  override def /(rhs: TopCoproduct): TopCoproduct = (expr, rhs) match
    case (ENum(i), rhsDyn: DynRepr) =>
      rhsDyn.expr match
        case ENum(j) if j != 0 => new DynRepr(ENum(i / j).withNormalized)
        case _ => new DynRepr(EBinOp("/", expr, rhsDyn.code, Sta))
    case _ =>
      new DynRepr(EBinOp("/", code, rhs.code, Sta))

  override def code: Expr = expr

def dyn(expr: Expr)(using c: Cache): TopCoproduct =
  if (c.contains(expr)) new DynRepr(EVar(c(expr)))
  else new DynRepr(expr)

def evalPS(expr: Expr)(using c: Cache): TopCoproduct = expr match
  case EBinOp("+", e1, e2, _) => evalPS(e1) + evalPS(e2)
  case EBinOp("*", e1, e2, _) => evalPS(e1) * evalPS(e2)
  case EBinOp("-", e1, e2, _) => evalPS(e1) - evalPS(e2)
  case EBinOp("/", e1, e2, _) => evalPS(e1) / evalPS(e2)
  case EVar(x) if c.inv.contains(x) => evalPS(c.inv(x))
  case e => dyn(e)

def residualizePS(repr: TopCoproduct, σ: Store, k: Cont, γ: MCont)(using c: Cache): (Value, Store) =
  // println(s"residualizePS: residualizing ${repr.code} with repr = ${repr}")
  def residualizeExpr(e: Expr, σ: Store, k: Cont, γ: MCont): (Value, Store) =
    // This is basically an eval function
    e match
      case EBinOp(op, e1, e2, _) =>
        residualizeExpr(e1, σ, { case (VCode(v1), σ1, γ1) =>
          residualizeExpr(e2, σ1, { case (VCode(v2), σ2, γ2) =>
            reflect(EBinOp(op, v1, v2, Sta).withNormalized, σ2, k, γ2)
          }, γ1)
        }, γ)
      case e => reflect(e, σ, k, γ)
  residualizeExpr(repr.code, σ, k, γ)

def reflectPS(σ: Store, k: Cont, γ: MCont)(using c: Cache): Expr ⇀ (Value, Store) =
  case e@EBinOp(_, _, _, _) if Opt("ps") && !e.normalized => residualizePS(evalPS(e), σ, k, γ)

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

/*
def hoistLam(e: Expr, σ: Store, c: Cache, k: Cont, γ: MCont): (Value, Store) =
  println(s"HoistLam: e = $e")
  e match
    case ELam(x, argTy, body, retTy) =>
      hoist(body, σ, BiMap(EVar(x) -> x), {
        case (VCode(t1), σ1, c1, γ1) =>
          //reflect(ELam(x, argTy.erase, t1, retTy.erase), σ1, c1, (x, σ1, c1, γ1) => γ1(x, σ1), γ1)
          γ1(VCode(ELam(x, argTy.erase, t1, retTy.erase)), σ1)
      }, {
        case (VCode(t1), σ1) =>
          k(VCode(t1), σ1, c, γ)
        /*
          //renormalize(t1, σ1, c, k, γ)
        */
      })

def hoist(e: Expr, σ: Store, c: Cache, k: Cont, γ: MCont): (Value, Store) =
  val allVars = c.allVals
  println(s"Hoist: allVars = $allVars, e = $e")
  e match
    case ELet(x, rhs, body) if rhs.isPure && rhs.freeVar.intersect(allVars).isEmpty =>
      // rhs is pure and does not depend on variables in the lambda's scope,
      // so we can lift it out of the lambda
      println(s"  Hoist let-binding: $x = $rhs")
      // FIXME: this is still buggy
      hoist(body, σ, c, k, { case (VCode(body1), σ1) =>
          γ(VCode(ELet(x, rhs, body1)), σ1)
      })
      /*
      hoist(body, σ, c, {
        case (body1, σ1, c1, γ1) => k(body1, σ1, c1, {
          case (VCode(body2), σ1) =>
            γ1(VCode(ELet(x, rhs, body2)), σ1)
        })
      }, γ)
      */
    case ELet(x, rhs, body) =>
      println(s"  Drop let-binding: $x = $rhs")
      hoist(body, σ, c + (rhs -> x), {
        case (VCode(body1), σ1, c1, γ1) => k(VCode(ELet(x, rhs, body1)), σ1, c1, γ1)
      }, γ)
    case _ =>
      k(VCode(e), σ, c, γ)
*/

def lift(k: Cont)(v: Value, σ: Store, γ: MCont)(using c: Cache): (Value, Store) = v match
  case VUnit => reflect(EUnit, σ, k, γ)
  case VNum(i) => reflect(ENum(i), σ, k, γ)
  case VBool(b) => reflect(EBool(b), σ, k, γ)
  case VLoc(l) => reflect(ELoc(l), σ, k, γ)
  case VClo(x, argTy, body, retTy, ρf, ςf) =>
    val l = σ.size
    val y = fresh()
    if (Opt("lam-hoist"))
      /*
      //eval(body, ρf + (x -> l), ςf, σ + (l -> VCode(EVar(y))), c, (x, σ1, c1, γ1) => γ1(x, σ1), {
      reify(body, ρf + (x -> l), ςf, σ + (l -> VCode(EVar(y))), c, {
        case (VCode(t), σ2) =>
          hoistLam(ELam(y, argTy.erase, t, retTy.erase), σ2, c, k, γ)
          /*
          k(cd, σ2, c, γ)
          hoist(t, σ2, BiMap(EVar(y) -> y), {
            case (VCode(t1), σ1, c1, γ1) =>
              reflect(ELam(y, argTy.erase, t1, retTy.erase), σ1, c1, k, γ1)
          }, γ)
          */
          /*
          hoist(t, σ2, BiMap(EVar(y) -> y), {
            case (VCode(t1), σ1, c1, γ1) =>
              reflect(ELam(y, argTy.erase, t1, retTy.erase), σ1, c1, (x, σ1, c1, γ1) => γ1(x, σ1), γ1)
          }, {
            case (VCode(t1), σ1) =>
              k(VCode(t1), σ1, c, γ)
          })
          */
      })
      */
      ???
    else
      reify(body, ρf + (x -> l), ςf, σ + (l -> VCode(EVar(y))), {
        case (VCode(t), σ2) =>
          reflect(ELam(y, argTy.erase, t, retTy.erase), σ2, k, γ)
      })

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
        eval(e2, ρ, ς, σ1, { case (v2, σ2, γ2) =>
          val l = σ2.size
          eval(body, ρf + (x -> l), ςf, σ2 + (l -> v2), k, γ2)
        }, γ1)
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
      // TODO: does meta-continuation need to observe current cache here?
      reify(e, ρ, ς, σ, { case (VCode(t), σ2) =>
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
    case EIsApp(e) =>
      eval(e, ρ, ς, σ, {
        case (VCode(EVar(x)), σ1, γ1) =>
          summon[Cache].inv(x) match
            case EApp(_, _, _) => k(VBool(true), σ1, γ1)
            case _ => k(VBool(false), σ1, γ1)
        case (VCode(_), σ1, γ1) =>
          k(VBool(false), σ1, γ1)
      }, γ)

def eval(e: Expr): (Value, Store) =
  reset
  eval(e, Map(), Map(), Map(), (x, σ, γ) => γ(x, σ), (x, σ) => (x, σ))(using BiMap())
