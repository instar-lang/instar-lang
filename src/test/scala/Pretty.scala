package instar.parser

import munit.FunSuite

import instar.interp.Value.*
import instar.interp.eval
import instar.pretty

class PrettyTest extends FunSuite:
  test("parse then pretty-print preserves canonical program text") {
    val src = "let f{s1, s2} = fun@s1(x: Int @ s2) => x in f{1, 1} 2"
    val parsed = parse(src)
    val printed = pretty.expr(parsed)

    assertEquals(printed, src)
    assertEquals(parse(printed), parsed)
  }

  test("pretty prints complex application arguments with parentheses") {
    val src = "f x (y + 1)"
    val parsed = parse(src)

    assertEquals(pretty.expr(parsed), src)
  }

  test("pretty prints VCode as exact canonical syntax") {
    val (value, _) = eval(parse("lift{2}(1)"))
    val VCode(code) = value
    val printed = pretty.value(value)

    assertEquals(printed, "1")
    assertEquals(parse(printed), code)
  }

  test("pretty prints type and stage polymorphism syntax") {
    val srcs = List(
      "sfun{s} => lift{s}(1)",
      "tfun[t] => fun(x: t) => x",
      "f[Int]",
      "lift{2}(1)",
      "fun(x: forall[t]. t) => x",
      "fun(x: forall{s}. Int @ s) => x",
    )

    srcs.foreach { src =>
      val parsed = parse(src)
      assertEquals(pretty.expr(parsed), src, src)
      assertEquals(parse(pretty.expr(parsed)), parsed, src)
    }
  }
