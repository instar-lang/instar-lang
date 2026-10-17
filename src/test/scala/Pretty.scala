package instar.parser

import munit.FunSuite

import instar.interp.Value.*
import instar.interp.eval
import instar.pretty

class PrettyTest extends FunSuite:
  test("printing displays the expansion of Code") {
    val parsed = parse("fun(f: Code[Int@1 -> Int@2]) => f")
    assertEquals(pretty.expr(parsed), "fun(f: (Int @ 2 -> Int @ 2) @ 2) => f")
    assertEquals(parse(pretty.expr(parsed)), parsed)
  }

  test("printing preserves explicit outer stage annotations") {
    val parsed = parse("fun(f: (Int@2 -> Int@2)@2) => f")
    assertEquals(pretty.expr(parsed), "fun(f: (Int @ 2 -> Int @ 2) @ 2) => f")
    assertEquals(parse(pretty.expr(parsed)), parsed)
  }

  test("parse then pretty-print preserves canonical program text") {
    val src = "let f[s1, s2] = fun@s1(x: Int @ s2) => x in f[1, 1] 2"
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

  test("pretty printing preserves constrained stage binders and types") {
    for src <- List(
      "sfun[a] => sfun[b: a <= b] => fun(x: Int@a) => lift[b](x)",
      "let f[a, b: a <= b, b <= 2](x: Int@a): Int@b = lift[b](x) in f[1, 2](3)",
      "fun(f: forall[a]. forall[b: a <= b]. Int@a -> Int@b) => f",
    ) do
      val parsed = parse(src)
      assertEquals(parse(pretty.expr(parsed)), parsed)
  }

  test("stage joins round-trip with grouping and both operator spellings") {
    for src <- List(
      "sfun[a, b, c: a | b <= c] => lift[a | (b | c)](1)",
      "fun@(a ⊔ b)(x: Int@(a ⊔ b)): Int@(a ⊔ b) => x",
      "fun(f: forall[a, b, c: a | b <= c]. Int@(a | b)) => f[1 | 2]",
      "x +@(a | (b | c)) y",
    ) do
      val parsed = parse(src)
      assertEquals(parse(pretty.expr(parsed)), parsed)
  }

  test("pretty printing parenthesizes joined stage annotations") {
    val arithmetic = "lift[2](1) +@(1 | 2) lift[2](2)"
    assertEquals(pretty.expr(parse(arithmetic)), arithmetic)
    val function = "fun@(a | b)(x: Int @ (a | b)): Int @ (a | b) => x"
    assertEquals(pretty.expr(parse(function)), function)
    val application = "f x@(a | b)"
    assertEquals(pretty.expr(parse(application)), application)
  }

  test("pretty prints VCode as exact canonical syntax") {
    val (value, _) = eval(parse("lift[2](1)"))
    val VCode(code) = value
    val printed = pretty.value(value)

    assertEquals(printed, "1")
    assertEquals(parse(printed), code)
  }
