// Section 3.3: Direct-style staging via delimited control operators (shift/reset).
// Simulates shift/reset monadically; reify/reflect correspond to reset/shift.

package instar.delimited

import instar.counter.*
import instar.*

trait Monad[F[_]]:
  def pure[A](a: A): F[A]
  extension [A](fa: F[A])
    def flatMap[B](f: A => F[B]): F[B]
    def map[B](f: A => B): F[B] =
      fa.flatMap(a => pure(f(a)))

object Cont:
  opaque type Cont[R, A] = (A => R) => R
  def apply[R, A](run: (A => R) => R): Cont[R, A] = run

  def runCont[A](cont: Cont[A, A]): A = cont(identity)

  def pure[R, A](a: A): Cont[R, A] = Cont(k => k(a))

  def reset[R, A](cont: Cont[A, A]): Cont[R, A] =
    pure(runCont(cont))

  def shift[R, A](f: (A => Cont[R, R]) => Cont[R, R]): Cont[R, A] =
    Cont(k => runCont(f(a => pure(k(a)))))

  given contMonad[R]: Monad[[A] =>> Cont[R, A]] with
    def pure[A](a: A): Cont[R, A] = Cont.pure(a)

    extension [A](fa: Cont[R, A])
      def flatMap[B](f: A => Cont[R, B]): Cont[R, B] =
        Cont(k => fa(a => f(a)(k)))

      def withFilter(p: A => Boolean): Cont[R, A] =
        Cont(k => fa(a => if p(a) then k(a) else throw new MatchError(a)))

import Stage.*
import Expr.*
import Value.*
import Cont.*

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

def reflect(e: Expr): Cont[Value, Value] =
  val x = fresh()
  shift: k =>
    for case VCode(t) <- k(VCode(EVar(x)))
    yield VCode(ELet(x, e, t))

def reify(e: Expr, ρ: Env): Cont[Value, Value] =
  reset(eval(e, ρ))

def lift(v: Value): Cont[Value, Value] =
  v match
    case VUnit => reflect(EUnit)
    case VNum(i) => reflect(ENum(i))
    case VBool(b) => reflect(EBool(b))
    case VClo(x, body, ρf) =>
      val y = fresh()
      for
        case VCode(t) <- reify(body, ρf + (x -> VCode(EVar(y))))
        v2 <- reflect(ELam(y, t))
      yield v2

def eval(e: Expr, ρ: Env): Cont[Value, Value] =
  e match
    case EUnit => pure(VUnit)
    case ENum(i) => pure(VNum(i))
    case EBool(b) => pure(VBool(b))
    case EVar(x) => pure(ρ(x))
    case ELam(x, body) => pure(VClo(x, body, ρ))
    case EApp(e1, e2, Sta) =>
      for
        case VClo(x, body, ρf) <- eval(e1, ρ)
        v2 <- eval(e2, ρ)
        v3 <- eval(body, ρf + (x -> v2))
      yield v3
    case EApp(e1, e2, Dyn) =>
      for
        case VCode(x1) <- eval(e1, ρ)
        case VCode(x2) <- eval(e2, ρ)
        v3 <- reflect(EApp1(x1, x2))
      yield v3
    case ELift(e) =>
      for
        v1 <- eval(e, ρ)
        v2 <- lift(v1)
      yield v2
    case ERun(e) =>
      for
        case VCode(t) <- reify(e, ρ)
        v2 <- eval(t, Map())
      yield v2
    case ELet(x, rhs, body) =>
      for
        v1 <- eval(rhs, ρ)
        v2 <- eval(body, ρ + (x -> v1))
      yield v2
    case ECond(e1, e2, e3, Sta) =>
      for
        case VBool(b) <- eval(e1, ρ)
        v <- if b then eval(e2, ρ) else eval(e3, ρ)
      yield v
    case ECond(e1, e2, e3, Dyn) =>
      for
        case VCode(x1) <- eval(e1, ρ)
        case VCode(x2) <- reify(e2, ρ)
        case VCode(x3) <- reify(e3, ρ)
        v3 <- reflect(ECond1(x1, x2, x3))
      yield v3
    case EBinOp(op, e1, e2, Sta) =>
      for
        v1 <- eval(e1, ρ)
        v2 <- eval(e2, ρ)
      yield evalPrim(op, v1, v2)
    case EBinOp(op, e1, e2, Dyn) =>
      for
        case VCode(x1) <- eval(e1, ρ)
        case VCode(x2) <- eval(e2, ρ)
        v3 <- reflect(EBinOp1(op, x1, x2))
      yield v3

def eval(e: Expr): Value =
  clear
  runCont(eval(e, Map()))
