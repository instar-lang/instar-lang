package instar.interp

import instar.parser.parse
import org.apache.commons.math3.stat.regression.{OLSMultipleLinearRegression, SimpleRegression}

/** Sampling, regression and table rendering shared by the benchmarks. */
object BenchKit {
  /** An Instar program parameterised by the array size. */
  type Program = Int => String

  /** eval calls spent on `program(n)`; `prefix` holds the shared declarations. */
  def cost(prefix: String)(program: Program, n: Int): Long =
    EvalCounter.n = 0L
    eval(parse(prefix + "\n" + program(n)))
    EvalCounter.n

  /** Least-squares fit of `points`. */
  case class Fit(slope: Double, intercept: Double, r2: Double):
    override def toString: String =
      // A column without variance has no slope and no R², only a constant.
      if r2.isNaN then f"constant $intercept%.0f"
      else f"$slope%.2f n + $intercept%.1f (R² = $r2%.4f)"

  def fit(points: Seq[(Long, Long)]): Fit =
    val reg = SimpleRegression()
    points.foreach((x, y) => reg.addData(x.toDouble, y.toDouble))
    Fit(reg.getSlope, reg.getIntercept, reg.getRSquare)

  /** Least-squares fit of `cost ≈ a·n log2 n + b·n + c`. */
  case class Model(a: Double, b: Double, c: Double, r2: Double):
    override def toString: String =
      f"$a%.2f n log2 n + $b%.1f n + $c%.1f (R² = $r2%.4f)"

  def model(points: Seq[(Long, Long)]): Model =
    val reg = OLSMultipleLinearRegression()
    val xs = points.map { case (n, _) => Array(n.toDouble * log2(n), n.toDouble) }.toArray
    reg.newSampleData(points.map(_._2.toDouble).toArray, xs)
    val beta = reg.estimateRegressionParameters
    Model(beta(1), beta(2), beta(0), reg.calculateRSquared)

  private def log2(n: Long): Double = math.log(n) / math.log(2)

  /** Right-aligned table whose column widths follow the data. */
  def table(header: Seq[String], rows: Seq[Seq[String]]): String =
    val columns: List[List[String]] = rows.map(_.toList).toList.transpose
    val width: List[Int] =
      header.toList.zip(columns).map { case (title, column) =>
        (title :: column).map(_.length).max
      }
    def render(cells: List[String]): String =
      cells.zip(width).map { case (cell, w) => " " * (w - cell.length) + cell }.mkString(" | ")
    val separator = width.map("-" * _).mkString("-+-")
    val body = rows.map(row => render(row.toList)).toList
    ((render(header.toList) :: separator :: body) :+ separator).mkString("\n")
}
