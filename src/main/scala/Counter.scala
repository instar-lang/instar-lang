package instar.counter

class Counter:
  private var x: Int = 0
  def fresh(prefix: String): String =
    val n = x
    x += 1
    s"$prefix$n"
  def clear: Unit = x = 0

val counter: Counter = new Counter
val counterPS: Counter = new Counter

def fresh(prefix: String = "x") = counter.fresh(prefix)
def freshPS(prefix: String = "x") = counterPS.fresh(prefix)

def clear: Unit = 
  counter.clear
  counterPS.clear
