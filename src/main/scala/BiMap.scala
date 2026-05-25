package instar

case class BiMap[A, B](forward: Map[A, B], backward: Map[B, A]):
  def +(ab: (A, B)): BiMap[A, B] =
    BiMap(forward + ab, backward + ab.swap)
  def contains(a: A): Boolean = forward.contains(a)
  def apply(a: A): B = forward(a)
  def inv: BiMap[B, A] = BiMap(backward, forward)
  def allKeys: Set[A] = forward.keySet
  def allVals: Set[B] = backward.keySet

object BiMap:
  def empty[A, B]: BiMap[A, B] = BiMap(Map(), Map())
  def apply[A, B](pairs: (A, B)*): BiMap[A, B] =
    pairs.foldLeft(empty[A, B]) { case (bm, (a, b)) => bm + (a -> b) }
