package instar.interp

import BenchKit.*

/** §5.2 sum of squares: sample the pipelines and fit a line to the eval calls. */
class Stream52Bench extends Stream52Base {
  private val decls: String =
    stream52(
      pairDecl,
      streamShapeDecl,
      stStreamDecl,
      incrDecl,
      ofArrDecl,
      mapDecl,
      foldDecl,
      sumOfSquaresDecl,
      iotaDecl,
    )("")

  // iota(n) and the declaration setup cancel out in the difference.
  private val base: Program = n => s"let a = iota($n) in a"

  /** Nothing is staged: the pipeline runs at stage 1. */
  private val unstaged: Program = n =>
    s"""
    let a = iota($n) in
    sumOfSquares[1](a)
    """

  /** First stage only: the code is generated, but never applied. */
  private val stagedFst: Program = n =>
    s"""
    let a = iota($n) in
    let squares = run(sumOfSquares[2]) in
    a
    """

  /** Both stages: generate the code, then run it on the array. */
  private val stagedTotal: Program = n =>
    s"""
    let a = iota($n) in
    let squares = run(sumOfSquares[2]) in
    squares(a)
    """

  private case class Row(
      size: Long,
      unstaged: Long,
      firstStage: Long,
      secondStage: Long,
      total: Long,
  )

  test("sum of squares: sampled eval calls and the fitted slopes") {
    // Powers of two; 2^15 is the deepest the 1 GB test-JVM stack reaches.
    val sizes = (0 to 15).map(1 << _).toList

    val rows = sizes.map { n =>
      val baseline = cost(decls)(base, n)
      val unstagedCost = cost(decls)(unstaged, n) - baseline
      val firstStageCost = cost(decls)(stagedFst, n) - baseline
      val totalCost = cost(decls)(stagedTotal, n) - baseline
      Row(n, unstagedCost, firstStageCost, totalCost - firstStageCost, totalCost)
    }

    val columns = List(
      "unstaged" -> rows.map(row => (row.size, row.unstaged)),
      "staged (fst)" -> rows.map(row => (row.size, row.firstStage)),
      "staged (snd)" -> rows.map(row => (row.size, row.secondStage)),
      "staged" -> rows.map(row => (row.size, row.total)),
    )

    val cells = rows.map { row =>
      val exponent = java.lang.Long.numberOfTrailingZeros(row.size)
      List(
        s"2^$exponent",
        row.unstaged.toString,
        row.firstStage.toString,
        row.secondStage.toString,
        row.total.toString,
      )
    }
    println(table("n" :: columns.map(_._1), cells))
    println("cost:")
    columns.foreach { case (name, points) => println(f"  $name%-13s= ${fit(points)}") }
  }
}
