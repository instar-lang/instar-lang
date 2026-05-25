package instar.egg

import instar.syntax.*
import instar.syntax.Expr.*
import instar.BiMap
import instar.Counter.fresh

// A non-functional unionfind
final class UnionFind[A](items: Iterable[A]) {
  val parent = scala.collection.mutable.Map[A, A]()
  val size = scala.collection.mutable.Map[A, Int]()

  items.foreach { x =>
    parent(x) = x
    size(x) = 1
  }

  def find(x: A): A = {
    val p = parent.getOrElseUpdate(x, {
      size(x) = 1
      x
    })

    if (p == x) x
    else {
      val root = find(p)
      parent(x) = root
      root
    }
  }

  def union(a: A, b: A): Unit = {
    val ra = find(a)
    val rb = find(b)

    if (ra != rb) {
      if (size(ra) < size(rb)) {
        parent(ra) = rb
        size(rb) += size(ra)
      } else {
        parent(rb) = ra
        size(ra) += size(rb)
      }
    }
  }

  def connected(a: A, b: A): Boolean =
    find(a) == find(b)
}

type Cache = BiMap[Expr, String]

case class Egg(cache: Cache, unionFind: UnionFind[String]):
  def findOptimal(x: String): String =
    val root = unionFind.find(x)
    val candidates = cache.allVals.filter(y => unionFind.find(y) == unionFind.find(root))
    println(s"findOptimal($x): candidates = ${candidates.map(y => s"$y -> ${cache.inv(y)}").mkString(", ")}")
    if candidates.isEmpty then root
    else candidates.minBy(y => (cost(cache.inv(y)), nameOrder(y)))

  def +(ex: (Expr, String)): Egg =
    val (_, x) = ex
    unionFind.find(x)
    Egg(cache + ex, unionFind)

  def relate(e1: Expr, e2: Expr): Egg =
    val (egg1, x1) = classOf(e1, None)
    val (egg2, x2) = egg1.classOf(e2, Some(x1))
    unionFind.union(x1, x2)
    egg2

  private def classOf(e: Expr, preferred: Option[String]): (Egg, String) =
    e match
      case EVar(x) =>
        unionFind.find(x)
        if cache.inv.contains(x) then (this, x) else (this + (e -> x), x)
      case _ if cache.contains(e) =>
        val x = cache(e)
        unionFind.find(x)
        (this, x)
      case _ =>
        val x = preferred.getOrElse(fresh())
        (this + (e -> x), x)

  private def cost(e: Expr): Int =
    e match
      case EUnit | ENum(_) | EBool(_) | EVar(_) => 1
      case ESLam(_, body) => 1 + cost(body)
      case ESApp(e, _) => 1 + cost(e)
      case ELam(_, _, body, _) => 1 + cost(body)
      case EBNLam(_, _, body, _) => 1 + cost(body)
      case EApp(e1, e2, _) => 1 + cost(e1) + cost(e2)
      case ELift(t, _) => 1 + cost(t)
      case ERun(t) => 1 + cost(t)
      case ELet(_, rhs, body) => 1 + cost(rhs) + cost(body)
      case ELetRec(_, rhs, body) => 1 + cost(rhs) + cost(body)
      case ECond(e1, e2, e3, _) => 1 + cost(e1) + cost(e2) + cost(e3)
      case EBinOp(_, e1, e2, _) => 1 + cost(e1) + cost(e2)
      case EUnaryOp(_, e, _) => 1 + cost(e)
      case EAlloc(e, _) => 1 + cost(e)
      case EDeref(e, _) => 1 + cost(e)
      case EAssign(e1, e2, _) => 1 + cost(e1) + cost(e2)
      case EAscribe(e, _) => cost(e)
      case EFix(_, e, _) => 1 + cost(e)
      case ELoc(_) => 1
      case EIsApp(e) => 1 + cost(e)
      case ECBNApp(e1, e2) => 1 + cost(e1) + cost(e2)

  private def nameOrder(x: String): (String, Int, String) =
    val (prefix, suffix) = x.span(!_.isDigit)
    val n = suffix.toIntOption.getOrElse(Int.MaxValue)
    (prefix, n, x)


object Egg:
  def apply(ex: (Expr, String)): Egg = 
    Egg() + ex
  def apply(): Egg =
    Egg(BiMap.empty, new UnionFind(Nil))


