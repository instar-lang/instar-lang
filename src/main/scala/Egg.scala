package instar.egg

import instar.syntax.*
import instar.syntax.Expr.*
import instar.BiMap

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

  def allItems: Iterable[A] =
    parent.keys
}

type Cache = BiMap[Expr, String]

case class Egg(cache: Cache, unionFind: UnionFind[Expr]):
  def findOptimal(e: Expr): Expr =
    val root = unionFind.find(e)
    val candidates = unionFind.allItems.filter(candidate => unionFind.find(candidate) == root)
    println(s"findOptimal($e): candidates = ${candidates.mkString(", ")}")
    if candidates.isEmpty then e
    else candidates.minBy(candidateKey)

  def +(ex: (Expr, String)): Egg =
    val (e, x) = ex
    val v = EVar(x)
    unionFind.union(e, v)
    Egg(cache + ex, unionFind)

  def relate(e1: Expr, e2: Expr): Egg =
    // If under the current cache, two expressions stand for same computation, we can relate them in the egraph.
    // e.g. if we have let x2 = x1 + x0, then we can relate x2 and x1 + x0 in the egraph.
    unionFind.union(e1, e2)
    this

  private def candidateKey(e: Expr): (Int, Int, String) =
    (candidateCost(e), candidateRank(e), e.toString)

  private def candidateCost(e: Expr): Int =
    e match
      case EVar(x) if cache.inv.contains(x) && cache.inv(x) != e =>
        cost(cache.inv(x))
      case _ =>
        cost(e)

  private def candidateRank(e: Expr): Int =
    e match
      case EVar(_) => 0
      case EUnit | ENum(_) | EBool(_) | ELoc(_) => 1
      case _ => 2

  private def cost(e: Expr): Int =
    // cost model
    e match
      case EUnit | ENum(_) | EBool(_) | EVar(_) => 1 // TODO: EVar should not be just 1, the cost of EVar should look up the cache
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

object Egg:
  def apply(ex: (Expr, String)): Egg = 
    Egg() + ex
  def apply(): Egg =
    Egg(BiMap.empty, new UnionFind(Nil))

