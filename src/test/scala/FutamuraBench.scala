package instar.interp

import BenchKit.*

/** §Futamura's first projection: sample factorial and fit the eval calls. */
class FutamuraBench extends FutamuraBase {
  private val decls: String =
    futamuraSource(
      exprDecl,
      listDecl,
      programDecl,
      lookupDecl,
      evalDecl,
      buildFunTableDecl,
      evalProgramDecl,
      factorialDecl,
    )("")

  // The AST and the declaration setup cancel out in the difference.
  private val base: Program = _ => "0"

  /** Nothing is staged: the interpreter walks the AST at stage 1. */
  private val unstaged: Program = n =>
    s"""
    let f = evalProgram[1](factorial) in
    f($n)
    """

  /** First stage only: the code is generated, but never applied. */
  private val stagedFst: Program = _ =>
    s"""
    let f = run(evalProgram[2](factorial)) in
    0
    """

  /** Both stages: generate the code, then run it on the input. */
  private val stagedTotal: Program = n =>
    s"""
    let f = run(evalProgram[2](factorial)) in
    f($n)
    """

  private case class Row(
      n: Long,
      unstaged: Long,
      firstStage: Long,
      secondStage: Long,
      total: Long,
  )

  test("factorial: sampled eval calls and the fitted lines") {
    // One call per level, so the cost is linear in n; 2^15 overflows the 1 GB
    // test stack.  The product wraps past 20!, but only the call count is read.
    val sizes = (4 to 14).map(1 << _).toList

    val rows = sizes.map { n =>
      val setup = cost(decls)(base, n)
      val unstagedCost = cost(decls)(unstaged, n) - setup
      val firstStageCost = cost(decls)(stagedFst, n) - setup
      val totalCost = cost(decls)(stagedTotal, n) - setup
      Row(n, unstagedCost, firstStageCost, totalCost - firstStageCost, totalCost)
    }

    val columns = List(
      "unstaged" -> rows.map(row => (row.n, row.unstaged)),
      "staged (fst)" -> rows.map(row => (row.n, row.firstStage)),
      "staged (snd)" -> rows.map(row => (row.n, row.secondStage)),
      "staged" -> rows.map(row => (row.n, row.total)),
    )

    val cells = rows.map { row =>
      val exponent = java.lang.Long.numberOfTrailingZeros(row.n)
      List(s"2^$exponent", row.unstaged, row.firstStage, row.secondStage, row.total)
        .map(_.toString)
    }
    println(table("n" :: columns.map(_._1), cells))
    println("cost:")
    columns.foreach { case (name, points) => println(f"  $name%-13s= ${fit(points)}") }
  }
}
