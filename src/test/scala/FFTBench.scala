package instar.interp

import BenchKit.*

/** §FFT radix-2 FFT: sample the transforms and fit `n log n` to the eval calls. */
class FFTBench extends FFTBase {
  private val decls: String =
    fftSource(
      complexDecl,
      pairDecl,
      tabulateDecl,
      seriesDecl,
      sineSeriesDecl,
      piDecl,
      sineDecl,
      omegaDecl,
      splitEvenOddDecl,
      butterflyDecl,
      fftSplitDecl,
      deinterleaveDecl,
      interleaveDecl,
      fftDecl,
    )("")

  // `tabulate` and the declaration setup cancel out in the difference.
  private val base: Program = n =>
    s"""
    let a = tabulate[Float](${2 * n})(fun(i: Int) => toFloat(i)) in
    a
    """

  /** Nothing is staged: the transform runs at stage 1. */
  private val unstaged: Program = n =>
    s"""
    let a = tabulate[Float](${2 * n})(fun(i: Int) => toFloat(i)) in
    fft[1]($n)(a)
    """

  /** First stage only: the code is generated, but never applied. */
  private val stagedFst: Program = n =>
    s"""
    let a = tabulate[Float](${2 * n})(fun(i: Int) => toFloat(i)) in
    let f = run(fft[2]($n)) in
    a
    """

  /** Both stages: generate the code, then run it on the array. */
  private val stagedTotal: Program = n =>
    s"""
    let a = tabulate[Float](${2 * n})(fun(i: Int) => toFloat(i)) in
    let f = run(fft[2]($n)) in
    f(a)
    """

  private case class Row(
      size: Long,
      unstaged: Long,
      firstStage: Long,
      secondStage: Long,
      total: Long,
  )

  test("FFT: sampled eval calls and the fitted model") {
    // Powers of two; `n = 2` is the base case and does not follow the model.
    val sizes = (2 to 9).map(1 << _).toList

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
    columns.foreach { case (name, points) => println(f"  $name%-13s= ${model(points)}") }
  }
}
