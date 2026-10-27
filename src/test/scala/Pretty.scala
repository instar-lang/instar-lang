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
