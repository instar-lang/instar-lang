package instar.typing

import munit.IgnoreSuite
import munit.FunSuite

import instar.interp.Value
import instar.parser.parse
import instar.pretty
import instar.syntax.*
import instar.syntax.given
import Expr.*
import Stage.*
import StageConstraints.*
import Type.*

@IgnoreSuite
class Fixme extends FunSuite:
  test("multiple stage vars") {
    {
      val str = """
        let f[s1, s2] = fun@s1(x: Int @ s2) => x in
        f[2, 2]
      """
      val checked = infer(parse(str))
      assert(Nil.implyTyEq(checked.ty.get, TFun(TInt.at(Dyn), TInt.at(Dyn)).at(Dyn)))
    }
    {
      val str = """
        let f[s1] [s2] = fun@s1(x: Int @ s2) => x in
        f[1][1]
      """
      val checked = infer(parse(str))
      assert(Nil.implyTyEq(checked.ty.get, TFun(TInt, TInt).at()))
    }
  }

  test("elaboration - stage var") {
    val expr = """let add[s] (x: Int@s) (y: Int) = x + y in add"""
    val inferred = infer(parse(expr))
    // Currently it fails to infer/elab.
    // Possible result 1: x +@s lift[s](y)
    // Possible result 2: add[s, s=1] (x: Int@s) (y: Int) = x +@1 y
    // Which one is better? The former is more general, and does not
    // restrict the instantiation of `s`.
    println(inferred.ty.get)
  }

class TypingTest extends FunSuite:
  test("Code and explicit stage annotations have equivalent meanings") {
    val code = instar.parser.parseType("Code[Int@1 -> Int@2]")
    val annotated = instar.parser.parseType("(Int@2 -> Int@2)@2")
    assertEquals(code, annotated)
    assert(Nil.implyTyEq(code, annotated))
  }

  test("Code recursively interprets nested type annotations at stage 2") {
    val code = instar.parser.parseType("Code[(Int@1 -> Ref[Int@1])@1 -> Int@1]")
    val annotated = instar.parser.parseType("((Int@2 -> Ref[Int@2]@2)@2 -> Int@2)@2")
    assert(Nil.implyTyEq(code, annotated))
    assert(Nil.implyTyEq(instar.parser.parseType("Code[Code[Int@1 -> Int@1]]"),
      instar.parser.parseType("(Int@2 -> Int@2)@2")))
  }

  test("stage-poly function") {
    val str1 = "(let f[s] = fun@s(x: Int @ s) => x in let g[s] = f[s] in fun(unit: Unit) => g[2]) (())"
    val checked1 = infer(parse(str1))
    assert(Nil.implyTyEq(checked1.ty.get, TFun(TInt.at(Dyn), TInt.at(Dyn)).at(Dyn)))
    val str2 = """
      let f[s] = fun@s(x: Int @ s) => x in
      let g[s] = f[s] in
      g[1]
    """
    val checked2 = infer(parse(str2))
    assert(Nil.implyTyEq(checked2.ty.get, TFun(TInt, TInt).at()))
  }

  test("infer resolves omitted first-stage markers") {
    val typed = infer(parse("let inc = fun(x: Int): Int => x + 1 in inc(41)"))

    assert(Nil.implyTyEq(typed.ty.get, TInt.at()))
    assertEquals(pretty.expr(typed),
      "let inc (x: Int): Int = lift[1](lift[1 | 1](x) +@(1 | 1) lift[1 | 1](1)) in lift[1](inc " +
      "(lift[1](41))@1)")
  }

  test("ascription fills in the lambda result type") {
    val checked = infer(parse("((fun(x: Int) => x): Int -> Int)"))

    assert(Nil.implyTyEq(checked.ty.get, TFun(TInt, TInt).at()))
    assertEquals(pretty.expr(checked),
      "let $s0 (x: Int): Int = x in lift[1](fun($s1) => lift[1]($s0 (lift[1]($s1))@1))")
  }

  test("infer instantiates stage-polymorphic expressions") {
    val typed = infer(parse("(sfun[s] => lift[s](fun(x: Int @ s): Int @ s => x))[2]"))
    assert(Nil.implyTyEq(typed.ty.get, TFun(TInt.at(Dyn), TInt.at(Dyn)).at(Dyn)))
    val inst = typed.asInstanceOf[ESApp]
    assertEquals(inst.st, SNum(2))
  }

  test("infer handles annotated letrec from parser output") {
    val src = """
      letrec fact: Int -> Int =
        fun(n: Int): Int => if n <= 1 then 1 else n * fact(n - 1)
      in fact(5)
    """
    val typed = infer(parse(src))
    assert(Nil.implyTyEq(typed.ty.get, TInt.at()))
    assertEquals(pretty.expr(typed),
      "letrec@1 fact = lift[1](fun($s2: Int): Int => (let $s0 (n: Int): Int = lift[1](if@(1 | 1) " +
      "lift[1 | 1](n) <=@(1 | 1) lift[1 | 1](1) then lift[1 | 1 | 1 | (1 | 1)](1) else lift[1 | 1 | 1 " +
      "| (1 | 1)](lift[1 | 1](n) *@(1 | 1) lift[1 | 1](fact (lift[1](lift[1 | 1](n) -@(1 | 1) lift[1 | " +
      "1](1)))@1))) in lift[1](fun($s1) => lift[1]($s0 (lift[1]($s1))@1))) $s2@1) in lift[1](fact " +
      "(lift[1](5))@1)")
  }

  test("infer handles fix with an explicitly annotated recursive binder") {
    val src =
      "fix fib: Int -> Int. fun(n: Int) => if n <= 1 then 1 else n * fib(n - 1)"

    val typed = infer(parse(src))
    assert(Nil.implyTyEq(typed.ty.get, TFun(TInt, TInt).at()))
    assertEquals(pretty.expr(typed),
      "letrec@1 fib = lift[1](fun($s2: Int): Int => (let $s0 (n: Int): Int @ (1 | 1 | 1 | (1 | 1)) = " +
      "if@(1 | 1) lift[1 | 1](n) <=@(1 | 1) lift[1 | 1](1) then lift[1 | 1 | 1 | (1 | 1)](1) else " +
      "lift[1 | 1 | 1 | (1 | 1)](lift[1 | 1](n) *@(1 | 1) lift[1 | 1](fib (lift[1](lift[1 | 1](n) -@(1 " +
      "| 1) lift[1 | 1](1)))@1)) in lift[1](fun($s1) => lift[1]($s0 (lift[1]($s1))@1))) $s2@1) in let " +
      "$s3 = fib in lift[1](fun($s4) => lift[1]($s3 (lift[1]($s4))@1))")
  }

  test("ascription treats forall stage binders up to alpha-renaming") {
    val src = "fun(x: forall[a]. Int @ a): forall[a]. Int @ a => x"
    val expected =
      TFun(
        TForallSt("b", TAt(TInt, SVar("b"))),
        TForallSt("c", TAt(TInt, SVar("c"))),
      )

    assert(Nil.implyTyEq(infer(parse(src)).ty.get, expected))
    val checked = infer(parse(s"(($src): (forall[b]. Int @ b) -> (forall[c]. Int @ c))"))
    assert(Nil.implyTyEq(checked.ty.get, expected.at()))
    }

  test("stage poly add") {
    val expr = "(let add[s] (x: Int @ s) (y: Int @ s) = x +@s y in fun(unit: Unit) => add[2] (lift[2](2)) (lift[2](3))) (())"
    val inferred = infer(parse(expr))
    assert(Nil.implyTyEq(inferred.ty.get, TInt.at(Dyn)))
  }

  test("quantified constraints are compared up to alpha-renaming and entailment") {
    val ty = instar.parser.parseType("forall[s: 1 <= s, s <= 2]. Int@s")
    val expected = instar.parser.parseType("forall[t]. Int@t")
    assert(Nil.implyTyEq(ty, expected))
    assert(!Nil.implyTyEq(instar.parser.parseType("forall[s: 2 <= s]. Int@s"), expected))
  }

class ElabTest extends FunSuite:
  private def run(src: String): Value =
    instar.interp.eval(infer(parse(src)))._1

  test("application uses the parsed expansion of Code") {
    val src = "fun(f: Code[Int@1 -> Int@2]) => f(1)"
    val parsed = parse(src)
    val typed = infer(parsed)
    assertEquals(pretty.expr(parsed),
      "fun(f: (Int @ 2 -> Int @ 2) @ 2) => f 1")
    assertEquals(pretty.expr(typed),
      "fun(f: (Int @ 2 -> Int @ 2) @ 2): Int @ 2 => f (lift[2](1))@2")
    assert(Nil.implyTyEq(typed.ty.get,
      TFun(TFun(TInt.at(Dyn), TInt.at(Dyn)).at(Dyn), TInt.at(Dyn))))
    assertEquals(run(s"run(($src)(fun@2(x: Int@2) => x))"), Value.VNum(1))
  }

  test("stage substitution preserves expanded Code and join syntax") {
    {
      val src = "sfun[s] => fun(f: Code[Int@s -> Int@s]) => f(1)"
      assertEquals(pretty.expr(infer(parse(src))),
        "sfun[s] => fun(f: (Int @ 2 -> Int @ 2) @ 2): Int @ 2 => f (lift[2](1))@2")
      assertEquals(run(s"run(($src)[1](fun@2(x: Int@2) => x))"), Value.VNum(1))
      assertEquals(run(s"run(($src)[2](fun@2(x: Int@2) => x))"), Value.VNum(1))
    }
    {
      val src = "(sfun[s] => lift[s](1))[1 | 1]"
      val typed = infer(parse(src))
      assertEquals(typed.ty, Some(TAt(TInt, Sta | Sta)))
      assertEquals(pretty.expr(typed), "(sfun[s] => lift[s](1))[1 | 1]")
      assertEquals(run(src), Value.VNum(1))
    }
    {
      val src = "(sfun[s] => lift[s | 1](1))[2]"
      val typed = infer(parse(src))
      assertEquals(typed.ty, Some(TAt(TInt, Dyn | Sta)))
      assertEquals(pretty.expr(typed), "(sfun[s] => lift[s | 1](1))[2]")
      assertEquals(run(s"run($src)"), Value.VNum(1))
    }
    {
      val src = "(sfun[a, b] => lift[a | (b | a)](1))[2]"
      val typed = infer(parse(src))
      assertEquals(typed.ty,
        Some(TForallSt("b", TAt(TInt, Dyn | (SVar("b") | Dyn)))))
      assertEquals(pretty.expr(typed), "(sfun[a, b] => lift[a | (b | a)](1))[2]")
      assertEquals(run(s"run(($src)[1])"), Value.VNum(1))
    }
  }

  test("checking converts the elaborated term directly") {
    val typed = infer(parse("(1: Int@2)"))
    assertEquals(typed.ty, Some(TInt.at(Dyn)))
    assertEquals(pretty.expr(typed),
      "lift[2](1)")
    assertEquals(run("run((1: Int@2))"), Value.VNum(1))
  }

  test("lifting changes only the function's outer stage") {
    val typed = infer(parse("lift[2](fun(x: Int@2) => x)"))
    assertEquals(typed.ty, Some(TFun(TInt.at(Dyn), TInt.at(Dyn)).at(Dyn)))
    assertEquals(pretty.expr(typed),
      "fun@2(x: Int @ 2): Int @ 2 => x")
    assertEquals(run("run(lift[2](fun(x: Int@2) => x))(3)"), Value.VNum(3))
  }

  test("symbolic lifting preserves concrete component stages") {
    val src = "sfun[a] => lift[a](fun(x: Code[Int]) => x)"
    val typed = infer(parse(src))
    assertEquals(typed.ty,
      Some(TForallSt("a", TFun(TInt.at(Dyn), TInt.at(Dyn)).at(SVar("a"))).at()))
    assertEquals(pretty.expr(typed),
      "sfun[a] => fun@a(x: Int @ 2): Int @ 2 => x")
    assertEquals(run(s"run(($src)[1](3))"), Value.VNum(3))
    assertEquals(run(s"run(($src)[2])(3)"), Value.VNum(3))
  }

  test("let coerces its body to the binding's stage") {
    {
      val typed = infer(parse("let x = lift[2](1) in 2"))
      assertEquals(typed.ty, Some(TInt.at(Dyn)))
      assertEquals(pretty.expr(typed),
        "let x = lift[2](1) in lift[2](2)")
      assertEquals(run("run(let x = lift[2](1) in 2)"), Value.VNum(2))
    }
    {
      val typed = infer(parse("let x = 1 in 2"))
      assertEquals(typed.ty, Some(TInt.at(Sta)))
      assertEquals(pretty.expr(typed),
        "let x = 1 in lift[1](2)")
      assertEquals(run("let x = 1 in 2"), Value.VNum(2))
    }
  }

  test("explicit dynamic conditionals coerce both branches") {
    val src = "if@2 lift[2](true) then 1 else 2"
    val typed = infer(parse(src))
    assertEquals(typed.ty, Some(TInt.at(Dyn | Sta | Sta)))
    assertEquals(pretty.expr(typed),
      "if@2 lift[2](lift[2](true)) then lift[2 | 1 | 1](1) else lift[2 | 1 | 1](2)")
    assertEquals(run(s"run($src)"), Value.VNum(1))
  }

  test("conditionals preserve a common function base type") {
    val src = "if true then fun(x: Code[Int]) => x else fun@2(x: Code[Int]) => x"
    val typed = infer(parse(src))
    assertEquals(typed.ty, Some(TFun(TInt.at(Dyn), TInt.at(Dyn)).at(Sta | Sta | Dyn)))
    assertEquals(pretty.expr(typed),
      "if@1 true then let $s0 (x: Int @ 2): Int @ 2 = x in fun@(1 | 1 | 2)($s1) => lift[2]($s0 " +
      "(lift[2]($s1))@1) else let $s2 = fun@2(x: Int @ 2): Int @ 2 => x in fun@(1 | 1 | 2)($s3) => " +
      "lift[2]($s2 (lift[2]($s3))@2)")
    assertEquals(run(s"run(($src)(3))"), Value.VNum(3))
  }

  test("arithmetic operation") {
    {
      val src = "1 + lift[2](2)"
      val typed = infer(parse(src))
      assert(Nil.implyTyEq(typed.ty.get, TInt.at(Dyn)))
    assertEquals(pretty.expr(typed),
      "lift[1 | 2](1) +@(1 | 2) lift[1 | 2](lift[2](2))")
      assertEquals(run(s"run($src)"), Value.VNum(3))
    }

    {
      val src = "lift[2](1) + 2"
      val typed = infer(parse(src))
      assert(Nil.implyTyEq(typed.ty.get, TInt.at(Dyn)))
    assertEquals(pretty.expr(typed),
      "lift[2 | 1](lift[2](1)) +@(2 | 1) lift[2 | 1](2)")
      assertEquals(run(s"run($src)"), Value.VNum(3))
    }

    {
      val src = "let add[s](x: Int@s)(y: Int) = x + y in add[1](2)(3)"
      val typed = infer(parse(src))
      assertEquals(pretty.expr(typed),
        "let add[s] (x: Int @ s) (y: Int): Int -> Int @ (s | 1) = lift[s | 1](x) +@(s | 1) lift[s | " +
        "1](y) in lift[1](add[1] (lift[1](2))@1 (lift[1](3))@1)")
      assertEquals(run(src), Value.VNum(5))
    }

    {
      val src = "(let add[s] (x: Int @ s) (y: Int) = x + y in fun(unit: Unit) => add[2] 2 3) (())"
      val typed = infer(parse(src))
      assertEquals(pretty.expr(typed),
        "(let add[s] (x: Int @ s) (y: Int): Int -> Int @ (s | 1) = lift[s | 1](x) +@(s | 1) lift[s | " +
        "1](y) in let $s0 (unit: Unit): Int @ (2 | 1) = add[2] (lift[2](2))@1 (lift[1](3))@1 in " +
        "lift[1](fun($s1) => lift[2 | 1]($s0 (lift[1]($s1))@1))) (lift[1](()))@1")
      assertEquals(run(s"run($src)"), Value.VNum(5))
    }

    {
      val expr = "(let add[s] (x: Int @ s) (y: Int @ s) = x + y in fun(unit: Unit) => add[2] 2 3) (())"
      val inferred = infer(parse(expr))
      assertEquals(pretty.expr(inferred),
        "(let add[s] (x: Int @ s) (y: Int @ s): Int @ s -> Int @ (s | s) = lift[s | s](x) +@(s | s) " +
        "lift[s | s](y) in let $s0 (unit: Unit): Int @ (2 | 2) = add[2] (lift[2](2))@1 (lift[2](3))@1 " +
        "in lift[1](fun($s1) => lift[2 | 2]($s0 (lift[1]($s1))@1))) (lift[1](()))@1")
      assert(Nil.implyTyEq(inferred.ty.get, TInt.at(Dyn)))
    }

    {
      val src = "sfun[a, b, c, d: a <= c, b <= c, a <= d, b <= d] => fun(x: Int@a) => fun(y: Int@b) => x + y"
      val typed = infer(parse(src))
      assertEquals(pretty.expr(typed),
        "sfun[a] => sfun[b] => sfun[c] => sfun[d: a <= c, b <= c, a <= d, b <= d] => fun(x: Int @ a): " +
        "Int @ b -> Int @ (a | b) => fun(y: Int @ b): Int @ (a | b) => lift[a | b](x) +@(a | b) lift[a " +
        "| b](y)")
    }

    {
      val src = "sfun[a, b, c, d: a <= c, b <= c, a <= d, b <= d] => fun(x: Int@a) => fun(y: Int@b) => x +@2 y"
      val typed = infer(parse(src))
      assertEquals(pretty.expr(typed),
        "sfun[a] => sfun[b] => sfun[c] => sfun[d: a <= c, b <= c, a <= d, b <= d] => fun(x: Int @ a): " +
        "Int @ b -> Int @ 2 => fun(y: Int @ b): Int @ 2 => lift[2](x) +@2 lift[2](y)")
    }

    {
      val src = "let add[a, b](x: Int@a)(y: Int@b): Int@(a | b) = x + y in add[1, 1](2)(3)"
      val typed = infer(parse(src))
      assert(Nil.implyTyEq(typed.ty.get, TInt.at()))
    assertEquals(pretty.expr(typed),
      "let add[a, b] (x: Int @ a) (y: Int @ b): Int @ b -> Int @ (a | b) = lift[a | b](lift[a | b](x) " +
      "+@(a | b) lift[a | b](y)) in lift[1](add[1, 1] (lift[1](2))@1 (lift[1](3))@1)")
      assertEquals(run(src), Value.VNum(5))
    }

    {
      val src = "(let add[a, b] (x: Int @ a) (y: Int @ b): Int @ (a | b) = x + y in fun(unit: Unit) => add[1, 2] 2 3) (())"
      val typed = infer(parse(src))
      assert(Nil.implyTyEq(typed.ty.get, TInt.at(Dyn)))
    assertEquals(pretty.expr(typed),
      "(let add[a, b] (x: Int @ a) (y: Int @ b): Int @ b -> Int @ (a | b) = lift[a | b](lift[a | b](x) " +
      "+@(a | b) lift[a | b](y)) in let $s2 (unit: Unit): Int @ (1 | 2) = add[1, 2] (lift[1](2))@1 " +
      "(lift[2](3))@1 in lift[1](fun($s3) => lift[1 | 2]($s2 (lift[1]($s3))@1))) (lift[1](()))@1")
      assertEquals(run(s"run($src)"), Value.VNum(5))
    }

    {
      val src = "(let add[a, b] (x: Int @ a) (y: Int @ b): Int @ (a | b) = x + y in fun(unit: Unit) => add[2, 1] 2 3) (())"
      val typed = infer(parse(src))
      assert(Nil.implyTyEq(typed.ty.get, TInt.at(Dyn)))
    assertEquals(pretty.expr(typed),
      "(let add[a, b] (x: Int @ a) (y: Int @ b): Int @ b -> Int @ (a | b) = lift[a | b](lift[a | b](x) " +
      "+@(a | b) lift[a | b](y)) in let $s2 (unit: Unit): Int @ (2 | 1) = add[2, 1] (lift[2](2))@1 " +
      "(lift[1](3))@1 in lift[1](fun($s3) => lift[2 | 1]($s2 (lift[1]($s3))@1))) (lift[1](()))@1")
      assertEquals(run(s"run($src)"), Value.VNum(5))
    }

    {
      val src = "(let add[a, b] (x: Int @ a) (y: Int @ b): Int @ (a | b) = x + y in fun(unit: Unit) => add[2, 2] 2 3) (())"
      val typed = infer(parse(src))
      assert(Nil.implyTyEq(typed.ty.get, TInt.at(Dyn)))
    assertEquals(pretty.expr(typed),
      "(let add[a, b] (x: Int @ a) (y: Int @ b): Int @ b -> Int @ (a | b) = lift[a | b](lift[a | b](x) " +
      "+@(a | b) lift[a | b](y)) in let $s2 (unit: Unit): Int @ (2 | 2) = add[2, 2] (lift[2](2))@1 " +
      "(lift[2](3))@1 in lift[1](fun($s3) => lift[2 | 2]($s2 (lift[1]($s3))@1))) (lift[1](()))@1")
      assertEquals(run(s"run($src)"), Value.VNum(5))
    }
  }

  test("conditionals") {
    {
      val src = "if true then 1 else lift[2](2)"
      val typed = infer(parse(src))
      assert(Nil.implyTyEq(typed.ty.get, TInt.at(Dyn)))
    assertEquals(pretty.expr(typed),
      "if@1 true then lift[1 | 1 | 2](1) else lift[1 | 1 | 2](lift[2](2))")
      assertEquals(run(s"run($src)"), Value.VNum(1))
    }

    {
      val src = "if false then lift[2](1) else 2"
      val typed = infer(parse(src))
      assert(Nil.implyTyEq(typed.ty.get, TInt.at(Dyn)))
    assertEquals(pretty.expr(typed),
      "if@1 false then lift[1 | 2 | 1](lift[2](1)) else lift[1 | 2 | 1](2)")
      assertEquals(run(s"run($src)"), Value.VNum(2))
    }

    {
      val src = "if lift[2](true) then 1 else 2"
      val typed = infer(parse(src))
      assert(Nil.implyTyEq(typed.ty.get, TInt.at(Dyn)))
    assertEquals(pretty.expr(typed),
      "if@2 lift[2](true) then lift[2 | 1 | 1](1) else lift[2 | 1 | 1](2)")
      assertEquals(run(s"run($src)"), Value.VNum(1))
    }

    {
      val src = "let choose[s](b: Bool@s) = if b then 1 else 2 in choose[1](true)"
      val typed = infer(parse(src))
      assertEquals(pretty.expr(typed),
        "let choose[s] (b: Bool @ s): Int @ (s | 1 | 1) = if@s b then lift[s | 1 | 1](1) else lift[s | " +
        "1 | 1](2) in lift[1](choose[1] (lift[1](true))@1)")
      assertEquals(run(src), Value.VNum(1))
    }

    {
      val src = "(let choose[s] (b: Bool @ s) = if b then 1 else 2 in fun(unit: Unit) => choose[2] true) (())"
      val typed = infer(parse(src))
      assertEquals(pretty.expr(typed),
        "(let choose[s] (b: Bool @ s): Int @ (s | 1 | 1) = if@s b then lift[s | 1 | 1](1) else lift[s " +
        "| 1 | 1](2) in let $s0 (unit: Unit): Int @ (2 | 1 | 1) = choose[2] (lift[2](true))@1 in " +
        "lift[1](fun($s1) => lift[2 | 1 | 1]($s0 (lift[1]($s1))@1))) (lift[1](()))@1")
      assertEquals(run(s"run($src)"), Value.VNum(1))
    }

    {
      val src =
        "sfun[a, b, c, d: a <= c, b <= c, a <= d, b <= d] => " +
        "fun(x: Int@a) => fun(y: Int@b) => if lift[2](true) then x else y"
      val typed = infer(parse(src))
      assertEquals(pretty.expr(typed),
        "sfun[a] => sfun[b] => sfun[c] => sfun[d: a <= c, b <= c, a <= d, b <= d] => fun(x: Int @ a): " +
        "Int @ b -> Int @ (2 | a | b) => fun(y: Int @ b): Int @ (2 | a | b) => if@2 lift[2](true) then " +
        "lift[2 | a | b](x) else lift[2 | a | b](y)")
    }

    {
      val src = "let choose[a, b, c](p: Bool@a)(x: Int@b)(y: Int@c) = if p then x else y in choose[1, 1, 1](false)(3)(4)"
      val typed = infer(parse(src))
      assert(Nil.implyTyEq(typed.ty.get, TInt.at()))
    assertEquals(pretty.expr(typed),
      "let choose[a, b, c] (p: Bool @ a) (x: Int @ b) (y: Int @ c): Int @ b -> Int @ c -> Int @ (a | b " +
      "| c) = if@a p then lift[a | b | c](x) else lift[a | b | c](y) in lift[1](choose[1, 1, 1] " +
      "(lift[1](false))@1 (lift[1](3))@1 (lift[1](4))@1)")
      assertEquals(run(src), Value.VNum(4))
    }

    {
      val src = "(let choose[a, b, c] (p: Bool @ a) (x: Int @ b) (y: Int @ c) = if p then x else y in fun(unit: Unit) => choose[1, 1, 2] false 3 4) (())"
      val typed = infer(parse(src))
      assert(Nil.implyTyEq(typed.ty.get, TInt.at(Dyn)))
    assertEquals(pretty.expr(typed),
      "(let choose[a, b, c] (p: Bool @ a) (x: Int @ b) (y: Int @ c): Int @ b -> Int @ c -> Int @ (a | " +
      "b | c) = if@a p then lift[a | b | c](x) else lift[a | b | c](y) in let $s0 (unit: Unit): Int @ " +
      "(1 | 1 | 2) = choose[1, 1, 2] (lift[1](false))@1 (lift[1](3))@1 (lift[2](4))@1 in " +
      "lift[1](fun($s1) => lift[1 | 1 | 2]($s0 (lift[1]($s1))@1))) (lift[1](()))@1")
      assertEquals(run(s"run($src)"), Value.VNum(4))
    }

    {
      val src = "(let choose[a, b, c] (p: Bool @ a) (x: Int @ b) (y: Int @ c) = if p then x else y in fun(unit: Unit) => choose[1, 2, 1] false 3 4) (())"
      val typed = infer(parse(src))
      assert(Nil.implyTyEq(typed.ty.get, TInt.at(Dyn)))
    assertEquals(pretty.expr(typed),
      "(let choose[a, b, c] (p: Bool @ a) (x: Int @ b) (y: Int @ c): Int @ b -> Int @ c -> Int @ (a | " +
      "b | c) = if@a p then lift[a | b | c](x) else lift[a | b | c](y) in let $s0 (unit: Unit): Int @ " +
      "(1 | 2 | 1) = choose[1, 2, 1] (lift[1](false))@1 (lift[2](3))@1 (lift[1](4))@1 in " +
      "lift[1](fun($s1) => lift[1 | 2 | 1]($s0 (lift[1]($s1))@1))) (lift[1](()))@1")
      assertEquals(run(s"run($src)"), Value.VNum(4))
    }

    {
      val src = "(let choose[a, b, c] (p: Bool @ a) (x: Int @ b) (y: Int @ c) = if p then x else y in fun(unit: Unit) => choose[1, 2, 2] false 3 4) (())"
      val typed = infer(parse(src))
      assert(Nil.implyTyEq(typed.ty.get, TInt.at(Dyn)))
    assertEquals(pretty.expr(typed),
      "(let choose[a, b, c] (p: Bool @ a) (x: Int @ b) (y: Int @ c): Int @ b -> Int @ c -> Int @ (a | " +
      "b | c) = if@a p then lift[a | b | c](x) else lift[a | b | c](y) in let $s0 (unit: Unit): Int @ " +
      "(1 | 2 | 2) = choose[1, 2, 2] (lift[1](false))@1 (lift[2](3))@1 (lift[2](4))@1 in " +
      "lift[1](fun($s1) => lift[1 | 2 | 2]($s0 (lift[1]($s1))@1))) (lift[1](()))@1")
      assertEquals(run(s"run($src)"), Value.VNum(4))
    }

    {
      val src = "(let choose[a, b, c] (p: Bool @ a) (x: Int @ b) (y: Int @ c) = if p then x else y in fun(unit: Unit) => choose[2, 1, 1] false 3 4) (())"
      val typed = infer(parse(src))
      assert(Nil.implyTyEq(typed.ty.get, TInt.at(Dyn)))
    assertEquals(pretty.expr(typed),
      "(let choose[a, b, c] (p: Bool @ a) (x: Int @ b) (y: Int @ c): Int @ b -> Int @ c -> Int @ (a | " +
      "b | c) = if@a p then lift[a | b | c](x) else lift[a | b | c](y) in let $s0 (unit: Unit): Int @ " +
      "(2 | 1 | 1) = choose[2, 1, 1] (lift[2](false))@1 (lift[1](3))@1 (lift[1](4))@1 in " +
      "lift[1](fun($s1) => lift[2 | 1 | 1]($s0 (lift[1]($s1))@1))) (lift[1](()))@1")
      assertEquals(run(s"run($src)"), Value.VNum(4))
    }

    {
      val src = "(let choose[a, b, c] (p: Bool @ a) (x: Int @ b) (y: Int @ c) = if p then x else y in fun(unit: Unit) => choose[2, 1, 2] false 3 4) (())"
      val typed = infer(parse(src))
      assert(Nil.implyTyEq(typed.ty.get, TInt.at(Dyn)))
    assertEquals(pretty.expr(typed),
      "(let choose[a, b, c] (p: Bool @ a) (x: Int @ b) (y: Int @ c): Int @ b -> Int @ c -> Int @ (a | " +
      "b | c) = if@a p then lift[a | b | c](x) else lift[a | b | c](y) in let $s0 (unit: Unit): Int @ " +
      "(2 | 1 | 2) = choose[2, 1, 2] (lift[2](false))@1 (lift[1](3))@1 (lift[2](4))@1 in " +
      "lift[1](fun($s1) => lift[2 | 1 | 2]($s0 (lift[1]($s1))@1))) (lift[1](()))@1")
      assertEquals(run(s"run($src)"), Value.VNum(4))
    }

    {
      val src = "(let choose[a, b, c] (p: Bool @ a) (x: Int @ b) (y: Int @ c) = if p then x else y in fun(unit: Unit) => choose[2, 2, 1] false 3 4) (())"
      val typed = infer(parse(src))
      assert(Nil.implyTyEq(typed.ty.get, TInt.at(Dyn)))
    assertEquals(pretty.expr(typed),
      "(let choose[a, b, c] (p: Bool @ a) (x: Int @ b) (y: Int @ c): Int @ b -> Int @ c -> Int @ (a | " +
      "b | c) = if@a p then lift[a | b | c](x) else lift[a | b | c](y) in let $s0 (unit: Unit): Int @ " +
      "(2 | 2 | 1) = choose[2, 2, 1] (lift[2](false))@1 (lift[2](3))@1 (lift[1](4))@1 in " +
      "lift[1](fun($s1) => lift[2 | 2 | 1]($s0 (lift[1]($s1))@1))) (lift[1](()))@1")
      assertEquals(run(s"run($src)"), Value.VNum(4))
    }

    {
      val src = "(let choose[a, b, c] (p: Bool @ a) (x: Int @ b) (y: Int @ c) = if p then x else y in fun(unit: Unit) => choose[2, 2, 2] false 3 4) (())"
      val typed = infer(parse(src))
      assert(Nil.implyTyEq(typed.ty.get, TInt.at(Dyn)))
    assertEquals(pretty.expr(typed),
      "(let choose[a, b, c] (p: Bool @ a) (x: Int @ b) (y: Int @ c): Int @ b -> Int @ c -> Int @ (a | " +
      "b | c) = if@a p then lift[a | b | c](x) else lift[a | b | c](y) in let $s0 (unit: Unit): Int @ " +
      "(2 | 2 | 2) = choose[2, 2, 2] (lift[2](false))@1 (lift[2](3))@1 (lift[2](4))@1 in " +
      "lift[1](fun($s1) => lift[2 | 2 | 2]($s0 (lift[1]($s1))@1))) (lift[1](()))@1")
      assertEquals(run(s"run($src)"), Value.VNum(4))
    }

    {
      val str = """
        if lift[2](true) then 1 else 2
      """
      val checked = infer(parse(s"(($str): Code[Int])"))
      assertEquals(pretty.expr(checked),
        "lift[2](if@2 lift[2](true) then lift[2 | 1 | 1](1) else lift[2 | 1 | 1](2))")
    }
  }

  test("constrained promotion from stage 1 to stage 1") {
    val src = "let promote[a, b: a <= b](x: Int@a) = lift[b](x) in promote[1, 1](3)"
    val typed = infer(parse(src))
    assertEquals(pretty.expr(typed),
      "let promote[a, b: a <= b] (x: Int @ a): Int @ b = lift[b](x) in lift[1](promote[1, 1] " +
      "(lift[1](3))@1)")
    assertEquals(run(src), Value.VNum(3))
  }

  test("constrained promotion from stage 1 to stage 2") {
    val src = "(let promote[a, b: a <= b] (x: Int @ a) = lift[b](x) in fun(unit: Unit) => promote[1, 2] 3) (())"
    val typed = infer(parse(src))
    assertEquals(pretty.expr(typed),
      "(let promote[a, b: a <= b] (x: Int @ a): Int @ b = lift[b](x) in let $s0 (unit: Unit): Int @ 2 " +
      "= promote[1, 2] (lift[1](3))@1 in lift[1](fun($s1) => lift[2]($s0 (lift[1]($s1))@1))) " +
      "(lift[1](()))@1")
    assertEquals(run(s"run($src)"), Value.VNum(3))
  }

  test("constrained promotion from stage 2 to stage 2") {
    val src = "(let promote[a, b: a <= b] (x: Int @ a) = lift[b](x) in fun(unit: Unit) => promote[2, 2] 3) (())"
    val typed = infer(parse(src))
    assertEquals(pretty.expr(typed),
      "(let promote[a, b: a <= b] (x: Int @ a): Int @ b = lift[b](x) in let $s0 (unit: Unit): Int @ 2 " +
      "= promote[2, 2] (lift[2](3))@1 in lift[1](fun($s1) => lift[2]($s0 (lift[1]($s1))@1))) " +
      "(lift[1](()))@1")
    assertEquals(run(s"run($src)"), Value.VNum(3))
  }

  test("stage joins retain their syntax under transitive constraints") {
    val src = "sfun[a, b, c: a <= b, b <= c] => fun(x: Int@a) => fun(y: Int@c) => x + y"
    assertEquals(pretty.expr(infer(parse(src))),
      "sfun[a] => sfun[b] => sfun[c: a <= b, b <= c] => fun(x: Int @ a): Int @ c -> Int @ (a | c) => " +
      "fun(y: Int @ c): Int @ (a | c) => lift[a | c](x) +@(a | c) lift[a | c](y)")
    val program = s"run(($src)[1, 1, 2](3)(4))"
    assertEquals(run(program), Value.VNum(7))

    val bounded = infer(parse("sfun[s: 2 <= s] => fun(x: Int@s) => x + lift[2](1)"))
    assertEquals(pretty.expr(bounded),
      "sfun[s: 2 <= s] => fun(x: Int @ s): Int @ (s | 2) => lift[s | 2](x) +@(s | 2) lift[s | " +
      "2](lift[2](1))")
  }

  test("entailment combines constraints from separate stage bindings") {
    val src = "sfun[a] => sfun[b: a <= b] => sfun[c: b <= c] => fun(x: Int@a) => lift[c](x)"
    assertEquals(pretty.expr(infer(parse(src))),
      "sfun[a] => sfun[b: a <= b] => sfun[c: b <= c] => fun(x: Int @ a): Int @ c => lift[c](x)")
    assertEquals(run(s"run(($src)[1, 2, 2](3))"), Value.VNum(3))
  }

  test("shadowed stage bindings retain independent constraints") {
    val src = "sfun[s: 2 <= s] => fun(x: Int@s) => sfun[s: s <= 1] => fun(y: Int@s) => x + y"
    assertEquals(pretty.expr(infer(parse(src))),
      "sfun[s: 2 <= s] => fun(x: Int @ s): forall[$s0: $s0 <= 1]. Int @ $s0 -> Int @ (s | $s0) => " +
      "sfun[$s0: $s0 <= 1] => fun(y: Int @ $s0): Int @ (s | $s0) => lift[s | $s0](x) +@(s | $s0) " +
      "lift[s | $s0](y)")
    assertEquals(run(s"run(($src)[2](3)[1](4))"), Value.VNum(7))
  }

  test("joined stage application instantiated at [1, 1]") {
    val src = "let id[s](x: Int@s) = x in let use[a, b](x: Int@(a | b)) = id[a | b](x) in use[1, 1](3)"
    val typed = infer(parse(src))
    assertEquals(pretty.expr(typed),
      "let id[s] (x: Int @ s): Int @ s = x in lift[1](let use[a, b] (x: Int @ (a | b)): Int @ (a | b) " +
      "= id[a | b] (lift[a | b](x))@1 in lift[1](use[1, 1] (lift[1 | 1](3))@1))")
    assertEquals(run(src), Value.VNum(3))
  }

  test("joined stage application instantiated at [1, 2]") {
    val src = "(let id[s] (x: Int @ s) = x in let use[a, b] (x: Int @ (a | b)) = id[a | b] x in fun(unit: Unit) => use[1, 2] 3) (())"
    val typed = infer(parse(src))
    assertEquals(pretty.expr(typed),
      "(let id[s] (x: Int @ s): Int @ s = x in let $s2 = let use[a, b] (x: Int @ (a | b)): Int @ (a | " +
      "b) = id[a | b] (lift[a | b](x))@1 in let $s0 (unit: Unit): Int @ (1 | 2) = use[1, 2] (lift[1 | " +
      "2](3))@1 in lift[1](fun($s1) => lift[1 | 2]($s0 (lift[1]($s1))@1)) in lift[1](fun($s3) => " +
      "lift[1 | 2]($s2 (lift[1]($s3))@1))) (lift[1](()))@1")
    assertEquals(run(s"run($src)"), Value.VNum(3))
  }

  test("joined constraint accepts [1, 2]") {
    val src = "let force[a, b: 2 <= a | b] = 1 in force[1, 2]"
    val typed = infer(parse(src))
    assertEquals(pretty.expr(typed),
      "let force[a, b: 2 <= a | b] = 1 in lift[1](force[1, 2])")
    assertEquals(run(src), Value.VNum(1))
  }

  test("joined constraint accepts [2, 1]") {
    val src = "let force[a, b: 2 <= a | b] = 1 in force[2, 1]"
    val typed = infer(parse(src))
    assertEquals(pretty.expr(typed),
      "let force[a, b: 2 <= a | b] = 1 in lift[1](force[2, 1])")
    assertEquals(run(src), Value.VNum(1))
  }

  test("joined constraint accepts [2, 2]") {
    val src = "let force[a, b: 2 <= a | b] = 1 in force[2, 2]"
    val typed = infer(parse(src))
    assertEquals(pretty.expr(typed),
      "let force[a, b: 2 <= a | b] = 1 in lift[1](force[2, 2])")
    assertEquals(run(src), Value.VNum(1))
  }

  test("join constraints compose transitively") {
    val src = "sfun[a, b, c, d: a <= b | c, b <= d, c <= d] => fun(x: Int@a) => lift[d](x)"
    val typed = infer(parse(src))
    assertEquals(pretty.expr(typed),
      "sfun[a] => sfun[b] => sfun[c] => sfun[d: a <= b | c, b <= d, c <= d] => fun(x: Int @ a): Int @ d => " +
      "lift[d](x)")
  }

  test("references preserve the stages of their element types") {
    {
      val src = "ref@2(lift[2](1))"
      val typed = infer(parse(src))
      assertEquals(typed.ty, Some(TRef(TInt.at(Dyn)).at(Dyn)))
      assertEquals(pretty.expr(typed), "ref@2(lift[2](1))")
    }
    {
      val src = "(ref@2(lift[2](1)): Code[Ref[Int]])"
      val typed = infer(parse(src))
      assertEquals(typed.ty, Some(TRef(TInt.at(Dyn)).at(Dyn)))
      assertEquals(pretty.expr(typed), "ref@2(lift[2](1))")
      assertEquals(run(s"run(!@2 $src)"), Value.VNum(1))
    }
    {
      val src = "!@2(ref@2(lift[2](1)))"
      val typed = infer(parse(src))
      assertEquals(typed.ty, Some(TInt.at(Dyn)))
      assertEquals(pretty.expr(typed), "!@2 ref@2(lift[2](1))")
      assertEquals(run(s"run($src)"), Value.VNum(1))
    }
    {
      val src = "!@1(ref@1(lift[2](1)))"
      val typed = infer(parse(src))
      assertEquals(typed.ty, Some(TInt.at(Dyn)))
      assertEquals(pretty.expr(typed), "!@1 ref@1(lift[2](1))")
      assertEquals(run(s"run($src)"), Value.VNum(1))
    }
    {
      val src = "ref@2(ref@2(lift[2](1)))"
      val typed = infer(parse(src))
      assertEquals(typed.ty, Some(TRef(TRef(TInt.at(Dyn)).at(Dyn)).at(Dyn)))
      assertEquals(pretty.expr(typed), "ref@2(ref@2(lift[2](1)))")
    }
    {
      val src = "sfun[s] => fun(r: Ref[Int@s]@s) => !@s r"
      val typed = infer(parse(src))
      assertEquals(pretty.expr(typed),
        "sfun[s] => fun(r: Ref[Int @ s] @ s): Int @ s => !@s r")
      assertEquals(run(s"($src)[1](ref@1(1))"), Value.VNum(1))
      assertEquals(run(s"run(($src)[2](ref@2(lift[2](1))))"), Value.VNum(1))
    }
  }

  test("reference stage join instantiated at [1, 1]") {
    val src =
      "let use[a, b] = let cell = ref@(a | b)(lift[a | b](1)) in let ignored = cell :=@(b | a) lift[a | b](2) in " +
      "!@(b | a) cell in use[1, 1]"
    val typed = infer(parse(src))
    assertEquals(pretty.expr(typed),
      "let use[a, b] = let cell = ref@(a | b)(lift[a | b](1)) in lift[a | b](let ignored = cell :=@(b " +
      "| a) lift[a | b](lift[a | b](2)) in lift[b | a](!@(b | a) cell)) in lift[1](use[1, 1])")
    assertEquals(run(src), Value.VNum(2))
  }

  test("reference stage join instantiated at [1, 2]") {
    val src =
      "(let use[a, b] = let cell = ref@(a | b)(lift[a | b](1)) in let ignored = cell :=@(b | a) lift[a | b](2) in " +
      "!@(b | a) cell in fun(unit: Unit) => use[1, 2])(())"
    val typed = infer(parse(src))
    assertEquals(pretty.expr(typed),
      "(let use[a, b] = let cell = ref@(a | b)(lift[a | b](1)) in lift[a | b](let ignored = cell :=@(b " +
      "| a) lift[a | b](lift[a | b](2)) in lift[b | a](!@(b | a) cell)) in let $s0 (unit: Unit): Int @ " +
      "(1 | 2) = use[1, 2] in lift[1](fun($s1) => lift[1 | 2]($s0 (lift[1]($s1))@1))) (lift[1](()))@1")
    assertEquals(run(s"run($src)"), Value.VNum(2))
  }

  test("reference stage join instantiated at [2, 1]") {
    val src =
      "(let use[a, b] = let cell = ref@(a | b)(lift[a | b](1)) in let ignored = cell :=@(b | a) lift[a | b](2) in " +
      "!@(b | a) cell in fun(unit: Unit) => use[2, 1])(())"
    val typed = infer(parse(src))
    assertEquals(pretty.expr(typed),
      "(let use[a, b] = let cell = ref@(a | b)(lift[a | b](1)) in lift[a | b](let ignored = cell :=@(b " +
      "| a) lift[a | b](lift[a | b](2)) in lift[b | a](!@(b | a) cell)) in let $s0 (unit: Unit): Int @ " +
      "(2 | 1) = use[2, 1] in lift[1](fun($s1) => lift[2 | 1]($s0 (lift[1]($s1))@1))) (lift[1](()))@1")
    assertEquals(run(s"run($src)"), Value.VNum(2))
  }

  test("reference stage join instantiated at [2, 2]") {
    val src =
      "(let use[a, b] = let cell = ref@(a | b)(lift[a | b](1)) in let ignored = cell :=@(b | a) lift[a | b](2) in " +
      "!@(b | a) cell in fun(unit: Unit) => use[2, 2])(())"
    val typed = infer(parse(src))
    assertEquals(pretty.expr(typed),
      "(let use[a, b] = let cell = ref@(a | b)(lift[a | b](1)) in lift[a | b](let ignored = cell :=@(b " +
      "| a) lift[a | b](lift[a | b](2)) in lift[b | a](!@(b | a) cell)) in let $s0 (unit: Unit): Int @ " +
      "(2 | 2) = use[2, 2] in lift[1](fun($s1) => lift[2 | 2]($s0 (lift[1]($s1))@1))) (lift[1](()))@1")
    assertEquals(run(s"run($src)"), Value.VNum(2))
  }

  test("function subtyping coerces arguments contravariantly and results covariantly") {
    val src = "fun(x: Code[Int]): Int => 7"
    val expected = TFun(TInt, TInt.at(Dyn))
    val typed = infer(parse(s"(($src): Int -> Code[Int])"))
    assertEquals(pretty.expr(typed),
      "let $s0 (x: Int @ 2): Int = lift[1](7) in lift[1](fun($s1) => lift[2]($s0 (lift[2]($s1))@1))")
    assert(Nil.implyTyEq(typed.ty.get, expected.at()))
    assertEquals(instar.interp.eval(ERun(EApp(typed, ENum(3), Some(Sta))))._1,
      Value.VNum(7))
    val lifted = infer(parse(s"(($src): Code[Int -> Int])"))
    assertEquals(pretty.expr(lifted),
      "let $s0 (x: Int @ 2): Int = lift[1](7) in fun@2($s1) => lift[2]($s0 (lift[2]($s1))@1)")
    assertEquals(instar.interp.eval(ERun(EApp(lifted, ELift(ENum(3), Dyn), Some(Dyn))))._1,
      Value.VNum(7))
  }

  test("fresh names restart for each program and remain distinct within a program") {
    val src = """
      let f: Int -> Code[Int] = fun(x: Code[Int]): Int => 1 in
      let g: Int -> Code[Int] = fun(y: Code[Int]): Int => 2 in g
    """
    val expected =
      "let f = let $s0 (x: Int @ 2): Int = lift[1](1) in lift[1](fun($s1) => lift[2]($s0 " +
      "(lift[2]($s1))@1)) in let $s6 = let g = let $s2 (y: Int @ 2): Int = lift[1](2) in " +
      "lift[1](fun($s3) => lift[2]($s2 (lift[2]($s3))@1)) in let $s4 = g in lift[1](fun($s5) => " +
      "lift[2]($s4 (lift[1]($s5))@1)) in lift[1](fun($s7) => lift[2]($s6 (lift[1]($s7))@1))"

    assertEquals(pretty.expr(infer(parse(src))),
      expected)
    assertEquals(pretty.expr(infer(parse(src))),
      expected)
  }

  test("function coercions evaluate their source once before calls") {
    val src = """
      let cell = ref(0) in
      let make(u: Unit): Int -> Int =
        let ignored = cell := !cell + 1 in fun(x: Int) => x in
      let f: Int -> Code[Int] = make(()) in
      (fun(first: Code[Int]) => (fun(second: Code[Int]) => !cell)(f(2)))(f(1))
    """
    assertEquals(pretty.expr(infer(parse(src))),
      "let cell = ref@1(0) in lift[1](let make = let $s4 (u: Unit): Int -> Int = let $s2 = let ignored " +
      "= cell :=@1 lift[1](lift[1 | 1](!@1 cell) +@(1 | 1) lift[1 | 1](1)) in let $s0 (x: Int): Int = " +
      "x in lift[1](fun($s1) => lift[1]($s0 (lift[1]($s1))@1)) in lift[1](fun($s3) => lift[1]($s2 " +
      "(lift[1]($s3))@1)) in lift[1](fun($s5) => let $s6 = $s4 (lift[1]($s5))@1 in lift[1](fun($s7) => " +
      "lift[1]($s6 (lift[1]($s7))@1))) in lift[1](let f = let $s8 = make (lift[1](()))@1 in " +
      "lift[1](fun($s9) => lift[2]($s8 (lift[1]($s9))@1)) in lift[1]((fun(first: Int @ 2): Int => " +
      "(fun(second: Int @ 2): Int => !@1 cell) (lift[2](f (lift[1](2))@1))@1) (lift[2](f " +
      "(lift[1](1))@1))@1)))")
    assertEquals(run(src), Value.VNum(1))
  }

  test("lifting respects stage ordering and is idempotent") {
    assertEquals(pretty.expr(infer(parse("lift[2](lift[2](1))"))),
      "lift[2](lift[2](1))")
    assertEquals(run("run(lift[2](lift[2](1)))"), Value.VNum(1))
  }

  test("run erases staged types in a closed code-producing expression") {
    val direct = "run(lift[2](fun(x: Code[Int]) => x))(3)"
    assertEquals(pretty.expr(infer(parse(direct))),
      "(run(fun@2(x: Int @ 2): Int @ 2 => x)) (lift[1](3))@1")
    assertEquals(run(direct), Value.VNum(3))
    val staged = "run((sfun[s] => fun@s(x: Code[Int]) => x)[2])(3)"
    val typed = infer(parse(staged))
    assertEquals(pretty.expr(typed),
      "(run((sfun[s] => fun@s(x: Int @ 2): Int @ 2 => x)[2])) (lift[1](3))@1")
    assert(Nil.implyTyEq(typed.ty.get, TInt.at()))
    assertEquals(run(staged), Value.VNum(3))
    val joined = "run((lift[2](1): Int@(1 | 2)))"
    assertEquals(pretty.expr(infer(parse(joined))),
      "run(lift[1 | 2](lift[2](1)))")
    assertEquals(run(joined), Value.VNum(1))
  }

  test("stage binders shadow without capturing outer stages or constraints") {
    val src = "sfun[s] => sfun[s: 2 <= s] => fun(x: Int@s) => x + 1"
    assertEquals(pretty.expr(infer(parse(src))),
      "sfun[s] => sfun[$s0: 2 <= $s0] => fun(x: Int @ $s0): Int @ ($s0 | 1) => lift[$s0 | 1](x) +@($s0 " +
      "| 1) lift[$s0 | 1](1)")
    assertEquals(run(s"run(($src)[1, 2](3))"), Value.VNum(4))
    val capture = "sfun[t] => fun(f: forall[s]. forall[t: s <= t]. Int@s -> Int@t) => f[t]"
    val expected = instar.parser.parseType(
      "forall[t]. (forall[s]. forall[u: s <= u]. Int@s -> Int@u) -> " +
      "(forall[u: t <= u]. Int@t -> Int@u)")
    val captured = infer(parse(capture))
    assertEquals(pretty.expr(captured),
      "sfun[t] => fun(f: forall[s]. forall[t: s <= t]. Int @ s -> Int @ t): forall[$s1: t <= $s1]. Int @ t -> " +
      "Int @ $s1 => f[t]")
    assert(Nil.implyTyEq(captured.ty.get, expected))
    val joinedCapture = "sfun[t, u] => fun(f: forall[s]. forall[t: s <= t]. Int@s -> Int@t) => f[t | u]"
    val joinedExpected = instar.parser.parseType(
      "forall[t]. forall[u]. (forall[s]. forall[v: s <= v]. Int@s -> Int@v) -> " +
      "(forall[v: t | u <= v]. Int@(t | u) -> Int@v)")
    val joined = infer(parse(joinedCapture))
    assertEquals(pretty.expr(joined),
      "sfun[t, u] => fun(f: forall[s]. forall[t: s <= t]. Int @ s -> Int @ t): forall[$s1: t | u <= $s1]. Int @ " +
      "(t | u) -> Int @ $s1 => f[t | u]")
    assert(Nil.implyTyEq(joined.ty.get, joinedExpected))
  }

  test("fix selects its stage from the declared recursive type") {
    val static = "fix f: Int -> Int. fun(n: Int) => if n <= 0 then 1 else f(n - 1)"
    assertEquals(pretty.expr(infer(parse(static))),
      "letrec@1 f = lift[1](fun($s2: Int): Int => (let $s0 (n: Int): Int @ (1 | 1 | 1 | 1) = if@(1 | " +
      "1) lift[1 | 1](n) <=@(1 | 1) lift[1 | 1](0) then lift[1 | 1 | 1 | 1](1) else lift[1 | 1 | 1 | " +
      "1](f (lift[1](lift[1 | 1](n) -@(1 | 1) lift[1 | 1](1)))@1) in lift[1](fun($s1) => lift[1]($s0 " +
      "(lift[1]($s1))@1))) $s2@1) in let $s3 = f in lift[1](fun($s4) => lift[1]($s3 (lift[1]($s4))@1))")
    assertEquals(run(s"($static)(3)"), Value.VNum(1))
    assertEquals(pretty.expr(infer(parse("fix@(1 | 1) f: Int -> Int. fun(n: Int) => n"))),
      "letrec@1 f = lift[1](fun($s2: Int): Int => (let $s0 (n: Int): Int = n in lift[1](fun($s1) => " +
      "lift[1]($s0 (lift[1]($s1))@1))) $s2@1) in let $s3 = f in lift[1](fun($s4) => lift[1]($s3 " +
      "(lift[1]($s4))@1))")
    val dynamic = "fix f: Code[Int -> Int]. fun@2(n: Code[Int]) => if n <= 0 then 1 else f(n - 1)"
    assertEquals(pretty.expr(infer(parse(dynamic))),
      "letrec@2 f = fun@2($s2: Int @ 2): Int @ 2 => (let $s0 = fun@2(n: Int @ 2): Int @ (2 | 1 | 1 | " +
      "2) => if@(2 | 1) lift[2 | 1](n) <=@(2 | 1) lift[2 | 1](0) then lift[2 | 1 | 1 | 2](1) else " +
      "lift[2 | 1 | 1 | 2](f (lift[2](lift[2 | 1](n) -@(2 | 1) lift[2 | 1](1)))@2) in fun@2($s1) => " +
      "lift[2]($s0 (lift[2]($s1))@2)) $s2@2 in let $s3 = f in fun@2($s4) => lift[2]($s3 " +
      "(lift[2]($s4))@2)")
    assertEquals(run(s"run(($dynamic)(3))"), Value.VNum(1))
  }

  test("fix preserves a symbolic outer stage") {
    val src = "sfun[s] => fix@s f: (Int@s -> Int@s)@s. " +
      "fun@s(n: Int@s) => if n <= 0 then 1 else f(n - 1)"
    assertEquals(pretty.expr(infer(parse(src))),
      "sfun[s] => letrec@s f = fun@s($s2: Int @ s): Int @ s => (let $s0 = fun@s(n: Int @ s): Int @ (s " +
      "| 1 | 1 | s) => if@(s | 1) lift[s | 1](n) <=@(s | 1) lift[s | 1](0) then lift[s | 1 | 1 | s](1) " +
      "else lift[s | 1 | 1 | s](f (lift[s](lift[s | 1](n) -@(s | 1) lift[s | 1](1)))@s) in fun@s($s1) " +
      "=> lift[s]($s0 (lift[s]($s1))@s)) $s2@s in let $s3 = f in fun@s($s4) => lift[s]($s3 " +
      "(lift[s]($s4))@s)")
    assertEquals(run(s"($src)[1](3)"), Value.VNum(1))
    assertEquals(run(s"run(($src)[2](lift[2](3)))"), Value.VNum(1))
  }

  test("fix preserves a joined outer stage") {
    val src = "sfun[a, b] => fix f: (Int@(a | b) -> Int@(a | b))@(a | b). " +
      "fun@(a | b)(x: Int@(a | b)) => x"
    assertEquals(pretty.expr(infer(parse(src))),
      "sfun[a, b] => letrec@(a | b) f = fun@(a | b)($s2: Int @ (a | b)): Int @ (a | b) => (let $s0 = " +
      "fun@(a | b)(x: Int @ (a | b)): Int @ (a | b) => x in fun@(a | b)($s1) => lift[a | b]($s0 " +
      "(lift[a | b]($s1))@(a | b))) $s2@(a | b) in let $s3 = f in fun@(a | b)($s4) => lift[a | b]($s3 " +
      "(lift[a | b]($s4))@(a | b))")
    assertEquals(run(s"($src)[1, 1](7)"), Value.VNum(7))
    assertEquals(run(s"run(($src)[1, 2](lift[2](7)))"), Value.VNum(7))
  }

  test("fix supports annotated polymorphic recursion") {
    val src = "fix f: forall[s]. Int -> Int@s. sfun[s] => fun(n: Int) => " +
      "if n <= 0 then lift[s](1) else f[s](n - 1)"
    assertEquals(pretty.expr(infer(parse(src))),
      "letrec@1 f[$s1] = (sfun[s] => fun(n: Int): Int @ (1 | 1 | s | s) => if@(1 | 1) lift[1 | 1](n) " +
      "<=@(1 | 1) lift[1 | 1](0) then lift[1 | 1 | s | s](lift[s](1)) else lift[1 | 1 | s | s](f[s] " +
      "(lift[1](lift[1 | 1](n) -@(1 | 1) lift[1 | 1](1)))@1))[$s1] in f")
    assertEquals(run(s"($src)[1](3)"), Value.VNum(1))
    assertEquals(run(s"run(($src)[2](3))"), Value.VNum(1))
  }

  test("fix delays a computed function body until calls") {
    {
      val src = """
        let cell = ref(0) in
        let f = fix f: Int -> Int.
          let ignored = cell := !cell + 1 in fun(n: Int) => n in
        let before = !cell in let first = f(1) in let second = f(2) in
        before * 100 + !cell
      """
      assertEquals(pretty.expr(infer(parse(src))),
        "let cell = ref@1(0) in lift[1](let f = letrec@1 f = lift[1](fun($s4: Int): Int => (let $s2 = " +
        "let ignored = cell :=@1 lift[1](lift[1 | 1](!@1 cell) +@(1 | 1) lift[1 | 1](1)) in let $s0 " +
        "(n: Int): Int = n in lift[1](fun($s1) => lift[1]($s0 (lift[1]($s1))@1)) in lift[1](fun($s3) " +
        "=> lift[1]($s2 (lift[1]($s3))@1))) $s4@1) in let $s5 = f in lift[1](fun($s6) => lift[1]($s5 " +
        "(lift[1]($s6))@1)) in lift[1](let before = !@1 cell in lift[1](let first = f (lift[1](1))@1 " +
        "in lift[1](let second = f (lift[1](2))@1 in lift[1](lift[1 | 1 | 1](lift[1 | 1](before) *@(1 " +
        "| 1) lift[1 | 1](100)) +@(1 | 1 | 1) lift[1 | 1 | 1](!@1 cell))))))")
      assertEquals(run(src), Value.VNum(2))
    }
    {
      val src = """
        let cell = ref@2(lift[2](0)) in
        letrec f: Code[Int -> Int] =
          let ignored = cell :=@2 !@2 cell + 1 in fun@2(n: Code[Int]) => n
        in let before = !@2 cell in let first = f(1) in let second = f(2) in
        before * 100 + !@2 cell
      """
      assertEquals(pretty.expr(infer(parse(src))),
        "let cell = ref@2(lift[2](0)) in lift[2](letrec@2 f = fun@2($s4: Int @ 2): Int @ 2 => (let $s2 " +
        "= let ignored = cell :=@2 lift[2](lift[2 | 1](!@2 cell) +@(2 | 1) lift[2 | 1](1)) in let $s0 " +
        "= fun@2(n: Int @ 2): Int @ 2 => n in fun@2($s1) => lift[2]($s0 (lift[2]($s1))@2) in " +
        "fun@2($s3) => lift[2]($s2 (lift[2]($s3))@2)) $s4@2 in lift[2](let before = !@2 cell in " +
        "lift[2](let first = f (lift[2](1))@2 in lift[2](let second = f (lift[2](2))@2 in " +
        "lift[2](lift[2 | 1 | 2](lift[2 | 1](before) *@(2 | 1) lift[2 | 1](100)) +@(2 | 1 | 2) lift[2 " +
        "| 1 | 2](!@2 cell))))))")
      assertEquals(run(s"run($src)"), Value.VNum(2))
    }
  }

  test("fix delays a computed polymorphic body until stage instantiation") {
    {
      val src = "fix f: forall[s]. Int@s -> Int@s. " +
        "if true then sfun[s] => fun(x: Int@s) => x else f"
      assertEquals(pretty.expr(infer(parse(src))),
        "letrec@1 f[$s4] = (if@1 true then sfun[s] => fun(x: Int @ s): Int @ s => x else f)[$s4] in f")
      assertEquals(run(s"($src)[1](3)"), Value.VNum(3))
      assertEquals(run(s"run(($src)[2](3))"), Value.VNum(3))
    }
    {
      val src = """
        let cell = ref(0) in
        letrec f: forall[s]. Int =
          let ignored = cell := !cell + 1 in sfun[s] => 1
        in let before = !cell in let first = f[1] in let second = f[2] in
        before * 100 + !cell
      """
      assertEquals(pretty.expr(infer(parse(src))),
        "let cell = ref@1(0) in lift[1](letrec@1 f[$s2] = (let ignored = cell :=@1 lift[1](lift[1 | " +
        "1](!@1 cell) +@(1 | 1) lift[1 | 1](1)) in sfun[s] => 1)[$s2] in lift[1](let before = !@1 cell " +
        "in lift[1](let first = f[1] in lift[1](let second = f[2] in lift[1](lift[1 | 1 | 1](lift[1 | " +
        "1](before) *@(1 | 1) lift[1 | 1](100)) +@(1 | 1 | 1) lift[1 | 1 | 1](!@1 cell))))))")
      assertEquals(run(src), Value.VNum(2))
    }
  }

  test("coerce primitives") {
    {
      val expr = parse("fun(x: Int): Int@2 => 1")
      val inferred = infer(expr)
      assertEquals(pretty.expr(inferred),
        "fun(x: Int): Int @ 2 => lift[2](1)")
    }
    {
      val expr = parse("fun(x: Int): Unit@2 => ()")
      val inferred = infer(expr)
      assertEquals(pretty.expr(inferred),
        "fun(x: Int): Unit @ 2 => lift[2](())")
    }
    {
      val expr = parse("fun(x: Int): Bool@2 => true")
      val inferred = infer(expr)
      assertEquals(pretty.expr(inferred),
        "fun(x: Int): Bool @ 2 => lift[2](true)")
    }
  }

  test("coerce var") {
    {
      val expr = parse("fun(x: Int): Int@2 => x")
      val inferred = infer(expr)
      assertEquals(pretty.expr(inferred),
        "fun(x: Int): Int @ 2 => lift[2](x)")
    }
    {
      val expr = parse("sfun[s] => fun(x: Int): Int@s => x")
      val inferred = infer(expr)
      assertEquals(pretty.expr(inferred),
        "sfun[s] => fun(x: Int): Int @ s => lift[s](x)")
    }
  }

class ElabNegativeTest extends FunSuite:
  test("references require well-formed element stages and matching operation stages") {
    intercept[TypeException] { infer(parse("fun(r: Ref[Int@1]@2) => r")) }
    intercept[TypeException] { infer(parse("sfun[s] => fun(r: Ref[Int]@s) => r")) }
    intercept[TypeException] { infer(parse("ref@2(1)")) }
    intercept[TypeException] { infer(parse("!@1(ref@2(lift[2](1)))")) }
    intercept[TypeException] { infer(parse("!@2(ref@1(lift[2](1)))")) }
    intercept[TypeException] { infer(parse("ref@2(lift[2](1)) :=@1 2")) }
    intercept[TypeException] { infer(parse("ref@1(lift[2](1)) :=@2 lift[2](2)")) }
  }

  test("function annotations cannot place components before the function") {
    intercept[TypeException] { infer(parse("fun(f: (Int@1 -> Int@1)@2) => f")) }
    intercept[TypeException] { infer(parse("fun(f: (Int@1 -> Int@2)@2) => f")) }
    intercept[TypeException] { infer(parse("fun(f: (Int@2 -> Int@1)@2) => f")) }
  }

  test("well-formedness checks expanded types and nested function annotations") {
    intercept[TypeException] {
      infer(parse("fun(f: ((Int@1 -> Int@1)@2 -> Int@2)@2) => f"))
    }
    intercept[TypeException] {
      infer(parse("fun(f: Code[forall[s]. Int@s]) => f"))
    }
  }

  test("let cannot lower the body's stage to the binding's stage") {
    intercept[TypeException] { infer(parse("let x = 1 in lift[2](2)")) }
  }

  test("conditionals require the same base function type in both orders") {
    intercept[TypeException] {
      infer(parse("if true then fun(x: Int): Code[Int] => x else fun(x: Code[Int]): Int => 1"))
    }
    intercept[TypeException] {
      infer(parse("if true then fun(x: Code[Int]): Int => 1 else fun(x: Int): Code[Int] => x"))
    }
  }

  test("a dynamic conditional cannot restage static function components") {
    intercept[TypeException] {
      infer(parse("if lift[2](true) then fun(x: Int) => x else fun(x: Int) => x"))
    }
  }

  test("infer rejects unannotated recursive letrec") {
    val src =
      "letrec fact = fun(n: Int) => if n <= 1 then 1 else n * fact(n - 1) in fact(5)"
    intercept[TypeException] { infer(parse(src)) }
  }

  test("fix requires an explicit recursive type") {
    intercept[TypeException] { infer(parse("fix f. fun(x: Int): Int => x")) }
  }

  test("fix rejects primitive and reference recursive types") {
    intercept[TypeException] { infer(parse("fix f: Int. 1")) }
    intercept[TypeException] { infer(parse("fix f: Ref[Int]. ref(0)")) }
  }

  test("fix checks its body against the declared recursive type") {
    intercept[TypeException] { infer(parse("fix f: Int -> Int. fun(x: Int) => false")) }
  }

  test("fix rejects an explicit stage that disagrees with its type") {
    intercept[TypeException] { infer(parse("fix@2 f: Int -> Int. fun(x: Int) => x")) }
    intercept[TypeException] { infer(parse("fix@1 f: Code[Int -> Int]. fun@2(x: Code[Int]) => x")) }
    intercept[TypeException] {
      infer(parse("sfun[s] => fix@1 f: (Int@s -> Int@s)@s. fun@s(x: Int@s) => x"))
    }
    intercept[TypeException] {
      infer(parse("fix@2 f: forall[s]. Int@s -> Int@s. sfun[s] => fun(x: Int@s) => x"))
    }
  }

  test("fix rejects ill-scoped recursive types") {
    intercept[TypeException] { infer(parse("fix f: Int@missing -> Int. fun(x: Int) => x")) }
  }

  test("checking rejects incompatible result types") {
    intercept[TypeException] { infer(parse("(1 < 2 : Code[Int])")) }
  }

  test("conditionals reject incompatible branch types") {
    intercept[TypeException] { infer(parse("if true then 1 else false")) }
  }

  test("conditionals reject ascription to an earlier stage") {
    intercept[TypeException] { infer(parse("((if lift[2](true) then 1 else 2): Int)")) }
  }

  test("stage applications reject backward promotion") {
    intercept[TypeException] {
      infer(parse("let promote[a, b: a <= b](x: Int@a) = lift[b](x) in promote[2, 1](lift[2](3))"))
    }
  }

  test("stage applications reject an unsatisfied joined constraint") {
    intercept[TypeException] { infer(parse("let force[a, b: 2 <= a | b] = 1 in force[1, 1]")) }
  }

  test("unsatisfiable constraints reject stage 1") {
    intercept[TypeException] { infer(parse("(sfun[s: 2 <= s, s <= 1] => 1)[1]")) }
  }

  test("unsatisfiable constraints reject stage 2") {
    intercept[TypeException] { infer(parse("(sfun[s: 2 <= s, s <= 1] => 1)[2]")) }
  }

  test("stage binders reject unbound variables") {
    intercept[TypeException] { infer(parse("sfun[s: s <= missing] => 1")) }
    intercept[TypeException] { infer(parse("sfun[a] => lift[a | missing](1)")) }
  }

  test("lifting requires stage ordering to follow from the constraints") {
    intercept[TypeException] { infer(parse("sfun[a, b] => fun(x: Int@a) => lift[b](x)")) }
    intercept[TypeException] {
      infer(parse("sfun[a, b, c: a <= b | c] => fun(x: Int@a) => lift[b](x)"))
    }
  }

  test("function subtyping rejects incompatible argument types") {
    intercept[TypeException] {
      infer(parse("((fun(x: Int): Int => x): Code[Int] -> Int)"))
    }
  }

  test("lifting rejects backward stages and unannotated functions") {
    intercept[TypeException] { infer(parse("lift[1](lift[2](1))")) }
    intercept[TypeException] { infer(parse("lift[2](fun(x: Int) => x)")) }
  }

  test("run rejects an open code-producing expression") {
    intercept[TypeException] { infer(parse("let x = lift[2](1) in run(x)")) }
  }

  test("shadowed stage binders retain their inner constraints") {
    val src = "sfun[s] => sfun[s: 2 <= s] => fun(x: Int@s) => x + 1"
    intercept[TypeException] { infer(parse(s"($src)[2, 1](1)")) }
  }
