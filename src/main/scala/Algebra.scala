package instar.algebra

import instar.syntax.*
import instar.Counter.fresh
import Expr.*
import Stage.*

extension [T](m1: Map[T, Int])
  def ⊔(m2: Map[T, Int]): Map[T, Int] =
    m1.foldLeft(m2) { case (acc, (k, v)) =>
      acc + (k -> (v + acc.getOrElse(k, 0)))
    }

trait Monoid[T]:
  def empty: T
  extension (x: T)
    def ⊗(rhs: T): T

trait Ring[T]:
  def zero: T
  def one: T

  extension (x: T)
    def ⊕(rhs: T): T
    def ⊗(rhs: T): T

trait Coproduct[Algebra[_], A: Algebra, B: Algebra]:
  type Coprod
  given ac: Algebra[Coprod]
  def inl(a: A): Coprod
  def inr(b: B): Coprod
  def eva[C: Algebra](fa: A => C, fb: B => C, co: Coprod): C

trait Free[Algebra[_], T]:
  type FreeA
  given af: Algebra[FreeA]
  def pvar(x: T): FreeA
  def pbind[C: Algebra](freeA: FreeA, f: T => C): C

def sta[Algebra[_], A: Algebra](a: A)(using f: Free[Algebra, Code], c: Coproduct[Algebra, A, f.FreeA]): c.Coprod =
  c.inl(a)

def code[Algebra[_], A: Algebra](code: Code)(using f: Free[Algebra, Code], c: Coproduct[Algebra, A, f.FreeA]): c.Coprod =
  c.inr(f.pvar(code))

def evaCode[Algebra[_], A: Algebra](f1: A => Code)(using f: Free[Algebra, Code], c: Coproduct[Algebra, A, f.FreeA])
                                   (f2: f.FreeA => Code, co: c.Coprod)(using Algebra[Code]): Code =
  c.eva(f1, f2, co)

def cd[Algebra[_], A: Algebra](using f: Free[Algebra, Code], a: Algebra[Expr], c: Coproduct[Algebra, A, f.FreeA], lift: Conversion[A, Expr])
                              (co: c.Coprod) =
  c.eva(lift, (frc) => f.pbind(frc, (x => x: Expr)), co)

case class MonomialRepr[T](vars: Map[T, Int])

// We can create free cmonoid for **any** type.
class FreeCMonoid[T] extends Free[Monoid, T]:
  type FreeA = MonomialRepr[T]

  given af: Monoid[FreeA] with
    def empty = MonomialRepr(Map())
    extension (x: FreeA)
      def ⊗(rhs: FreeA): FreeA = MonomialRepr(x.vars ⊔ rhs.vars)

  def pvar(x: T): FreeA = MonomialRepr(Map(x -> 1))

  def pbind[C: Monoid](freeA: FreeA, f: T => C): C =
    freeA.vars.foldLeft(summon[Monoid[C]].empty) { case (acc, (v, count)) =>
      val term = List.fill(count)(f(v)).reduce(_ ⊗ _)
      acc ⊗ term
    }

def initMN[R](n: Int)(using r: Ring[R]): R = n match
  case 0 => r.zero
  case 1 => r.one
  case n if n >= 0 =>
    val half = initMN(n / 2)
    if n % 2 == 0 then half ⊕ half else half ⊕ half ⊕ r.one

case class Multinomial[X, A](terms: Map[Map[X, Int], A])

type Code = Expr.EVar

// For any Ring[T], we can automatically get a Ring[Multinomial[X, T]]
given [X, T](using r: Ring[T]): Ring[Multinomial[X, T]] = new MultinomialRing[X, T]

given Ring[Int] with
  def zero: Int = 0
  def one: Int = 1

  extension (x: Int)
    def ⊕(rhs: Int): Int = x + rhs
    def ⊗(rhs: Int): Int = x * rhs

def evalMN[X, A, B](f1: A => B)(f2: X => B)(m: Multinomial[X, A])(using r1: Ring[A], r2: Ring[B]): B =
  def power(a: B, n: Int)(using r2: Ring[B]): B = n match
    case 0 => r2.one
    case 1 => a
    case n if n % 2 == 1 =>
      val x = power(a, (n - 1) / 2)
      x ⊗ x ⊗ a
    case _ =>
      val x = power(a, n / 2)
      x ⊗ x

  m.terms.toSeq
    .sortBy { case (xs, _) =>
      xs.toSeq.sortBy { case (x, n) => (x.toString, n) }.mkString("|")
    }
    .foldLeft(r2.zero) { case (sum, (xs, a)) =>
      val monomial = xs.toSeq
        .sortBy { case (x, n) => (x.toString, n) }
        .foldLeft(f1(a)) { case (prod, (x, n)) =>
          prod ⊗ power(f2(x), n)
        }

      sum ⊕ monomial
    }

// Multinomial itself is a ring structure
class MultinomialRing[X, T](using r: Ring[T]) extends Ring[Multinomial[X, T]]:
  def zero: Multinomial[X, T] = Multinomial(Map())
  def one: Multinomial[X, T] = Multinomial(Map(Map() -> r.one))

  extension (x: Multinomial[X, T])
    def ⊕(rhs: Multinomial[X, T]): Multinomial[X, T] =
      Multinomial(
        (x.terms.keySet ++ rhs.terms.keySet).map { k =>
          k -> (x.terms.getOrElse(k, r.zero) ⊕ rhs.terms.getOrElse(k, r.zero))
        }.toMap
      )

    def ⊗(rhs: Multinomial[X, T]): Multinomial[X, T] =
      x.terms.foldLeft(zero) { case (acc, (xs, c)) =>
        acc ⊕ rhs.terms.foldLeft(zero) { case (Multinomial(acc), (rxs, coeff)) =>
          Multinomial(acc + (rxs ⊔ xs -> c ⊗ coeff))
        }
      }

// Multinomial can be served as free extension of ring for any type
class FreeRing [T] extends Free[Ring, T]:
  type FreeA = Multinomial[T, Int]
  given af: Ring[FreeA] = new MultinomialRing[T, Int]
  def pvar(x: T): FreeA = Multinomial(Map(Map(x -> 1) -> 1))
  def pbind[C: Ring](freeA: FreeA, f: T => C): C =
    evalMN(initMN)(f)(freeA)

given productMonoid[A: Monoid, B: Monoid]: Monoid[(A, B)] with
  def empty: (A, B) = (summon[Monoid[A]].empty, summon[Monoid[B]].empty)
  extension (x: (A, B))
    def ⊗(rhs: (A, B)): (A, B) =
      val (a1, b1) = x
      val (a2, b2) = rhs
      (a1 ⊗ a2, b1 ⊗ b2)

// We can create a Coproduct of Monoid and FreeCMonoid.
given [A, B](using m: Monoid[A], f: Free[Monoid, B]): Coproduct[Monoid, A, f.FreeA] =
  new Coproduct[Monoid, A, f.FreeA]:
    type Coprod = (A, f.FreeA)
    given ac: Monoid[Coprod] = productMonoid[A, f.FreeA]
    def inl(a: A): Coprod = (a, summon[Monoid[f.FreeA]].empty)
    def inr(b: f.FreeA): Coprod = (m.empty, b)
    def eva[C: Monoid](fa: A => C, fb: f.FreeA => C, co: Coprod): C =
      fa(co._1) ⊗ fb(co._2)

// We can create a Coproduct of Ring and FreeRing.
given [A, B](using r: Ring[A], f: FreeRing[B]): Coproduct[Ring, A, f.FreeA] =
  new Coproduct[Ring, A, f.FreeA]:
    type Coprod = Multinomial[B, A]
    given ac: Ring[Coprod] = new MultinomialRing[B, A]
    def inl(a: A): Coprod = Multinomial(Map(Map.empty[B, Int] -> a))
    def inr(b: f.FreeA): Coprod = Multinomial(b.terms.map( { case (vars, coeff) =>
      vars -> initMN(coeff)(using r)
    }))
    def eva[C: Ring](fa: A => C, fb: f.FreeA => C, co: Coprod): C =
      evalMN(fa)((b: B) => fb(f.pvar(b)))(co)

given freeRingCode: FreeRing[Code] = new FreeRing[Code]

val AddMulRingCoproductImpl: Coproduct[Ring, Int, freeRingCode.FreeA] =
  summon[Coproduct[Ring, Int, freeRingCode.FreeA]]

object AddMulRingExprImpl extends Ring[Expr]:
  def zero: Expr = ENum(0)
  def one: Expr = ENum(1)

  def bindExpr(e: Expr)(k: Expr => Expr): Expr =
    e match
      case EUnit | ENum(_) | EBool(_) | EVar(_) => k(e)
      case ELet(x, rhs, body) => ELet(x, rhs, bindExpr(body)(k))
      case _ =>
        val x = fresh()
        ELet(x, e, k(EVar(x)))

  def anfBinOp(op: String, lhs: Expr, rhs: Expr): Expr =
    bindExpr(lhs) { lhsAtom =>
      bindExpr(rhs) { rhsAtom =>
        val x = fresh()
        ELet(x, EBinOp(op, lhsAtom, rhsAtom, Sta), EVar(x))
      }
    }

  extension (lhs: Expr)
    def ⊕(rhs: Expr): Expr =
      if (lhs == zero) rhs
      else if (rhs == zero) lhs
      else anfBinOp("+", lhs, rhs)

    def ⊗(rhs: Expr): Expr =
      if (lhs == one) rhs
      else if (rhs == one) lhs
      else if (lhs == zero || rhs == zero) zero
      else anfBinOp("*", lhs, rhs)

given Conversion[Int, Expr] with
  def apply(i: Int): Expr = ENum1(i)
