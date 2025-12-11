package spmp

object Counter:
  var x: Int = 0
  def fresh(prefix: String = "x"): String =
    val n = x
    x += 1
    s"$prefix$n"
  def reset: Unit = x = 0