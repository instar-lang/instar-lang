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
      "let inc (x: Int): Int = (fun($s2) => lift[1]($s2)) ((fun($s0) => lift[1 | 1]($s0)) x@1 +@(1 | 1) " +
      "(fun($s1) => lift[1 | 1]($s1)) 1@1)@1 in (fun($s4) => lift[1]($s4)) (inc ((fun($s3) => lift[1]($s3)) " +
      "41@1)@1)@1")
  }

  test("ascription fills in the lambda result type") {
    val checked = infer(parse("((fun(x: Int) => x): Int -> Int)"))

    assert(Nil.implyTyEq(checked.ty.get, TFun(TInt, TInt).at()))
    assertEquals(pretty.expr(checked),
      "(fun($s2) => lift[1](fun($s3) => (fun($s1) => lift[1]($s1)) ($s2 ((fun($s0) => lift[1]($s0)) " +
      "$s3@1)@1)@1)) (fun(x: Int): Int => x)@1")
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
      "letrec@1 fact = lift[1](fun($s14: Int): Int => (fun($s12) => lift[1](fun($s13) => (fun($s11) => " +
      "lift[1]($s11)) ($s12 ((fun($s10) => lift[1]($s10)) $s13@1)@1)@1)) (fun(n: Int): Int => (fun($s9) => " +
      "lift[1]($s9)) (if@(1 | 1) (fun($s0) => lift[1 | 1]($s0)) n@1 <=@(1 | 1) (fun($s1) => lift[1 | 1]($s1)) " +
      "1@1 then (fun($s7) => lift[1 | 1 | 1 | (1 | 1)]($s7)) 1@1 else (fun($s8) => lift[1 | 1 | 1 | (1 | " +
      "1)]($s8)) ((fun($s5) => lift[1 | 1]($s5)) n@1 *@(1 | 1) (fun($s6) => lift[1 | 1]($s6)) (fact ((fun($s4) " +
      "=> lift[1]($s4)) ((fun($s2) => lift[1 | 1]($s2)) n@1 -@(1 | 1) (fun($s3) => lift[1 | 1]($s3)) " +
      "1@1)@1)@1)@1)@1)@1)@1 $s14@1) in (fun($s16) => lift[1]($s16)) (fact ((fun($s15) => lift[1]($s15)) " +
      "5@1)@1)@1")
  }

  test("infer handles fix with an explicitly annotated recursive binder") {
    val src =
      "fix fib: Int -> Int. fun(n: Int) => if n <= 1 then 1 else n * fib(n - 1)"

    val typed = infer(parse(src))
    assert(Nil.implyTyEq(typed.ty.get, TFun(TInt, TInt).at()))
    assertEquals(pretty.expr(typed),
      "letrec@1 fib = lift[1](fun($s13: Int): Int => (fun($s11) => lift[1](fun($s12) => (fun($s10) => " +
      "lift[1]($s10)) ($s11 ((fun($s9) => lift[1]($s9)) $s12@1)@1)@1)) (fun(n: Int): Int @ (1 | 1 | 1 | (1 | 1))" +
      " => if@(1 | 1) (fun($s0) => lift[1 | 1]($s0)) n@1 <=@(1 | 1) (fun($s1) => lift[1 | 1]($s1)) 1@1 then " +
      "(fun($s7) => lift[1 | 1 | 1 | (1 | 1)]($s7)) 1@1 else (fun($s8) => lift[1 | 1 | 1 | (1 | 1)]($s8)) " +
      "((fun($s5) => lift[1 | 1]($s5)) n@1 *@(1 | 1) (fun($s6) => lift[1 | 1]($s6)) (fib ((fun($s4) => " +
      "lift[1]($s4)) ((fun($s2) => lift[1 | 1]($s2)) n@1 -@(1 | 1) (fun($s3) => lift[1 | 1]($s3)) " +
      "1@1)@1)@1)@1)@1)@1 $s13@1) in (fun($s16) => lift[1](fun($s17) => (fun($s15) => lift[1]($s15)) ($s16 " +
      "((fun($s14) => lift[1]($s14)) $s17@1)@1)@1)) fib@1")
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
      "fun(f: (Int @ 2 -> Int @ 2) @ 2): Int @ 2 => f ((fun($s0) => lift[2]($s0)) 1@1)@2")
    assert(Nil.implyTyEq(typed.ty.get,
      TFun(TFun(TInt.at(Dyn), TInt.at(Dyn)).at(Dyn), TInt.at(Dyn))))
    assertEquals(run(s"run(($src)(fun@2(x: Int@2) => x))"), Value.VNum(1))
  }

  test("stage substitution preserves expanded Code and join syntax") {
    {
      val src = "sfun[s] => fun(f: Code[Int@s -> Int@s]) => f(1)"
      assertEquals(pretty.expr(infer(parse(src))),
        "sfun[s] => fun(f: (Int @ 2 -> Int @ 2) @ 2): Int @ 2 => f ((fun($s0) => lift[2]($s0)) 1@1)@2")
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

  test("checking applies the coercion derived by subtyping") {
    val typed = infer(parse("(1: Int@2)"))
    assertEquals(typed.ty, Some(TInt.at(Dyn)))
    assertEquals(pretty.expr(typed),
      "(fun($s0) => lift[2]($s0)) 1@1")
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
        "let x = lift[2](1) in (fun($s0) => lift[2]($s0)) 2@1")
      assertEquals(run("run(let x = lift[2](1) in 2)"), Value.VNum(2))
    }
    {
      val typed = infer(parse("let x = 1 in 2"))
      assertEquals(typed.ty, Some(TInt.at(Sta)))
      assertEquals(pretty.expr(typed),
        "let x = 1 in (fun($s0) => lift[1]($s0)) 2@1")
      assertEquals(run("let x = 1 in 2"), Value.VNum(2))
    }
  }

  test("explicit dynamic conditionals coerce both branches") {
    val src = "if@2 lift[2](true) then 1 else 2"
    val typed = infer(parse(src))
    assertEquals(typed.ty, Some(TInt.at(Dyn | Sta | Sta)))
    assertEquals(pretty.expr(typed),
      "if@2 (fun($s0) => lift[2]($s0)) (lift[2](true))@1 then " +
      "(fun($s1) => lift[2 | 1 | 1]($s1)) 1@1 else (fun($s2) => lift[2 | 1 | 1]($s2)) 2@1")
    assertEquals(run(s"run($src)"), Value.VNum(1))
  }

  test("conditionals preserve a common function base type") {
    val src = "if true then fun(x: Code[Int]) => x else fun@2(x: Code[Int]) => x"
    val typed = infer(parse(src))
    assertEquals(typed.ty, Some(TFun(TInt.at(Dyn), TInt.at(Dyn)).at(Sta | Sta | Dyn)))
    assertEquals(pretty.expr(typed),
      "if@1 true then (fun($s2) => fun@(1 | 1 | 2)($s3) => (fun($s1) => lift[2]($s1)) ($s2 ((fun($s0) => " +
      "lift[2]($s0)) $s3@1)@1)@1) (fun(x: Int @ 2): Int @ 2 => x)@1 else (fun($s6) => fun@(1 | 1 | 2)($s7) => " +
      "(fun($s5) => lift[2]($s5)) ($s6 ((fun($s4) => lift[2]($s4)) $s7@1)@2)@1) (fun@2(x: Int @ 2): Int @ 2 => " +
      "x)@1")
    assertEquals(run(s"run(($src)(3))"), Value.VNum(3))
  }

  test("arithmetic operation") {
    {
      val src = "1 + lift[2](2)"
      val typed = infer(parse(src))
      assert(Nil.implyTyEq(typed.ty.get, TInt.at(Dyn)))
    assertEquals(pretty.expr(typed),
      "(fun($s0) => lift[1 | 2]($s0)) 1@1 +@(1 | 2) (fun($s1) => lift[1 | 2]($s1)) (lift[2](2))@1")
      assertEquals(run(s"run($src)"), Value.VNum(3))
    }

    {
      val src = "lift[2](1) + 2"
      val typed = infer(parse(src))
      assert(Nil.implyTyEq(typed.ty.get, TInt.at(Dyn)))
    assertEquals(pretty.expr(typed),
      "(fun($s0) => lift[2 | 1]($s0)) (lift[2](1))@1 +@(2 | 1) (fun($s1) => lift[2 | 1]($s1)) 2@1")
      assertEquals(run(s"run($src)"), Value.VNum(3))
    }

    {
      val src = "let add[s](x: Int@s)(y: Int) = x + y in add[1](2)(3)"
      val typed = infer(parse(src))
      assertEquals(pretty.expr(typed),
        "let add[s] (x: Int @ s) (y: Int): Int -> Int @ (s | 1) = (fun($s0) => lift[s | 1]($s0)) x@1 +@(s | 1) " +
        "(fun($s1) => lift[s | 1]($s1)) y@1 in (fun($s4) => lift[1]($s4)) (add[1] ((fun($s2) => lift[1]($s2)) " +
        "2@1)@1 ((fun($s3) => lift[1]($s3)) 3@1)@1)@1")
      assertEquals(run(src), Value.VNum(5))
    }

    {
      val src = "(let add[s] (x: Int @ s) (y: Int) = x + y in fun(unit: Unit) => add[2] 2 3) (())"
      val typed = infer(parse(src))
      assertEquals(pretty.expr(typed),
        "(let add[s] (x: Int @ s) (y: Int): Int -> Int @ (s | 1) = (fun($s0) => lift[s | 1]($s0)) x@1 +@(s | 1) " +
        "(fun($s1) => lift[s | 1]($s1)) y@1 in (fun($s6) => lift[1](fun($s7) => (fun($s5) => lift[2 | 1]($s5)) " +
        "($s6 ((fun($s4) => lift[1]($s4)) $s7@1)@1)@1)) (fun(unit: Unit): Int @ (2 | 1) => add[2] ((fun($s2) => " +
        "lift[2]($s2)) 2@1)@1 ((fun($s3) => lift[1]($s3)) 3@1)@1)@1) ((fun($s8) => lift[1]($s8)) (())@1)@1")
      assertEquals(run(s"run($src)"), Value.VNum(5))
    }

    {
      val expr = "(let add[s] (x: Int @ s) (y: Int @ s) = x + y in fun(unit: Unit) => add[2] 2 3) (())"
      val inferred = infer(parse(expr))
      assertEquals(pretty.expr(inferred),
        "(let add[s] (x: Int @ s) (y: Int @ s): Int @ s -> Int @ (s | s) = (fun($s0) => lift[s | s]($s0)) x@1 +@(s" +
        " | s) (fun($s1) => lift[s | s]($s1)) y@1 in (fun($s6) => lift[1](fun($s7) => (fun($s5) => lift[2 | " +
        "2]($s5)) ($s6 ((fun($s4) => lift[1]($s4)) $s7@1)@1)@1)) (fun(unit: Unit): Int @ (2 | 2) => add[2] " +
        "((fun($s2) => lift[2]($s2)) 2@1)@1 ((fun($s3) => lift[2]($s3)) 3@1)@1)@1) ((fun($s8) => lift[1]($s8)) " +
        "(())@1)@1")
      assert(Nil.implyTyEq(inferred.ty.get, TInt.at(Dyn)))
    }

    {
      val src = "sfun[a, b, c, d: a <= c, b <= c, a <= d, b <= d] => fun(x: Int@a) => fun(y: Int@b) => x + y"
      val typed = infer(parse(src))
      assertEquals(pretty.expr(typed),
        "sfun[a] => sfun[b] => sfun[c] => sfun[d: a <= c, b <= c, a <= d, b <= d] => fun(x: Int @ a): Int @ b -> " +
        "Int @ (a | b) => fun(y: Int @ b): Int @ (a | b) => (fun($s0) => lift[a | b]($s0)) x@1 +@(a | b) (fun($s1)" +
        " => lift[a | b]($s1)) y@1")
    }

    {
      val src = "sfun[a, b, c, d: a <= c, b <= c, a <= d, b <= d] => fun(x: Int@a) => fun(y: Int@b) => x +@2 y"
      val typed = infer(parse(src))
      assertEquals(pretty.expr(typed),
        "sfun[a] => sfun[b] => sfun[c] => sfun[d: a <= c, b <= c, a <= d, b <= d] => fun(x: Int @ a): Int @ b -> " +
        "Int @ 2 => fun(y: Int @ b): Int @ 2 => (fun($s0) => lift[2]($s0)) x@1 +@2 (fun($s1) => lift[2]($s1)) y@1")
    }

    {
      val src = "let add[a, b](x: Int@a)(y: Int@b): Int@(a | b) = x + y in add[1, 1](2)(3)"
      val typed = infer(parse(src))
      assert(Nil.implyTyEq(typed.ty.get, TInt.at()))
    assertEquals(pretty.expr(typed),
      "let add = (fun($s5) => $s5) (sfun[a, b] => fun(x: Int @ a): Int @ b -> Int @ (a | b) => fun(y: Int @ b): " +
      "Int @ (a | b) => (fun($s2) => lift[a | b]($s2)) ((fun($s0) => lift[a | b]($s0)) x@1 +@(a | b) (fun($s1) " +
      "=> lift[a | b]($s1)) y@1)@1)@1 in (fun($s8) => lift[1]($s8)) (add[1, 1] ((fun($s6) => lift[1]($s6)) " +
      "2@1)@1 ((fun($s7) => lift[1]($s7)) 3@1)@1)@1")
      assertEquals(run(src), Value.VNum(5))
    }

    {
      val src = "(let add[a, b] (x: Int @ a) (y: Int @ b): Int @ (a | b) = x + y in fun(unit: Unit) => add[1, 2] 2 3) (())"
      val typed = infer(parse(src))
      assert(Nil.implyTyEq(typed.ty.get, TInt.at(Dyn)))
    assertEquals(pretty.expr(typed),
      "(let add = (fun($s5) => $s5) (sfun[a, b] => fun(x: Int @ a): Int @ b -> Int @ (a | b) => fun(y: Int @ b):" +
      " Int @ (a | b) => (fun($s2) => lift[a | b]($s2)) ((fun($s0) => lift[a | b]($s0)) x@1 +@(a | b) (fun($s1) " +
      "=> lift[a | b]($s1)) y@1)@1)@1 in (fun($s10) => lift[1](fun($s11) => (fun($s9) => lift[1 | 2]($s9)) ($s10" +
      " ((fun($s8) => lift[1]($s8)) $s11@1)@1)@1)) (fun(unit: Unit): Int @ (1 | 2) => add[1, 2] ((fun($s6) => " +
      "lift[1]($s6)) 2@1)@1 ((fun($s7) => lift[2]($s7)) 3@1)@1)@1) ((fun($s12) => lift[1]($s12)) (())@1)@1")
      assertEquals(run(s"run($src)"), Value.VNum(5))
    }

    {
      val src = "(let add[a, b] (x: Int @ a) (y: Int @ b): Int @ (a | b) = x + y in fun(unit: Unit) => add[2, 1] 2 3) (())"
      val typed = infer(parse(src))
      assert(Nil.implyTyEq(typed.ty.get, TInt.at(Dyn)))
    assertEquals(pretty.expr(typed),
      "(let add = (fun($s5) => $s5) (sfun[a, b] => fun(x: Int @ a): Int @ b -> Int @ (a | b) => fun(y: Int @ b):" +
      " Int @ (a | b) => (fun($s2) => lift[a | b]($s2)) ((fun($s0) => lift[a | b]($s0)) x@1 +@(a | b) (fun($s1) " +
      "=> lift[a | b]($s1)) y@1)@1)@1 in (fun($s10) => lift[1](fun($s11) => (fun($s9) => lift[2 | 1]($s9)) ($s10" +
      " ((fun($s8) => lift[1]($s8)) $s11@1)@1)@1)) (fun(unit: Unit): Int @ (2 | 1) => add[2, 1] ((fun($s6) => " +
      "lift[2]($s6)) 2@1)@1 ((fun($s7) => lift[1]($s7)) 3@1)@1)@1) ((fun($s12) => lift[1]($s12)) (())@1)@1")
      assertEquals(run(s"run($src)"), Value.VNum(5))
    }

    {
      val src = "(let add[a, b] (x: Int @ a) (y: Int @ b): Int @ (a | b) = x + y in fun(unit: Unit) => add[2, 2] 2 3) (())"
      val typed = infer(parse(src))
      assert(Nil.implyTyEq(typed.ty.get, TInt.at(Dyn)))
    assertEquals(pretty.expr(typed),
      "(let add = (fun($s5) => $s5) (sfun[a, b] => fun(x: Int @ a): Int @ b -> Int @ (a | b) => fun(y: Int @ b):" +
      " Int @ (a | b) => (fun($s2) => lift[a | b]($s2)) ((fun($s0) => lift[a | b]($s0)) x@1 +@(a | b) (fun($s1) " +
      "=> lift[a | b]($s1)) y@1)@1)@1 in (fun($s10) => lift[1](fun($s11) => (fun($s9) => lift[2 | 2]($s9)) ($s10" +
      " ((fun($s8) => lift[1]($s8)) $s11@1)@1)@1)) (fun(unit: Unit): Int @ (2 | 2) => add[2, 2] ((fun($s6) => " +
      "lift[2]($s6)) 2@1)@1 ((fun($s7) => lift[2]($s7)) 3@1)@1)@1) ((fun($s12) => lift[1]($s12)) (())@1)@1")
      assertEquals(run(s"run($src)"), Value.VNum(5))
    }
  }

  test("conditionals") {
    {
      val src = "if true then 1 else lift[2](2)"
      val typed = infer(parse(src))
      assert(Nil.implyTyEq(typed.ty.get, TInt.at(Dyn)))
    assertEquals(pretty.expr(typed),
      "if@1 true then (fun($s0) => lift[1 | 1 | 2]($s0)) 1@1 else (fun($s1) => lift[1 | 1 | 2]($s1)) " +
      "(lift[2](2))@1")
      assertEquals(run(s"run($src)"), Value.VNum(1))
    }

    {
      val src = "if false then lift[2](1) else 2"
      val typed = infer(parse(src))
      assert(Nil.implyTyEq(typed.ty.get, TInt.at(Dyn)))
    assertEquals(pretty.expr(typed),
      "if@1 false then (fun($s0) => lift[1 | 2 | 1]($s0)) (lift[2](1))@1 else (fun($s1) => lift[1 | 2 | 1]($s1))" +
      " 2@1")
      assertEquals(run(s"run($src)"), Value.VNum(2))
    }

    {
      val src = "if lift[2](true) then 1 else 2"
      val typed = infer(parse(src))
      assert(Nil.implyTyEq(typed.ty.get, TInt.at(Dyn)))
    assertEquals(pretty.expr(typed),
      "if@2 lift[2](true) then (fun($s0) => lift[2 | 1 | 1]($s0)) 1@1 else (fun($s1) => lift[2 | 1 | 1]($s1)) " +
      "2@1")
      assertEquals(run(s"run($src)"), Value.VNum(1))
    }

    {
      val src = "let choose[s](b: Bool@s) = if b then 1 else 2 in choose[1](true)"
      val typed = infer(parse(src))
      assertEquals(pretty.expr(typed),
        "let choose[s] (b: Bool @ s): Int @ (s | 1 | 1) = if@s b then (fun($s0) => lift[s | 1 | 1]($s0)) 1@1 else " +
        "(fun($s1) => lift[s | 1 | 1]($s1)) 2@1 in (fun($s3) => lift[1]($s3)) (choose[1] ((fun($s2) => " +
        "lift[1]($s2)) true@1)@1)@1")
      assertEquals(run(src), Value.VNum(1))
    }

    {
      val src = "(let choose[s] (b: Bool @ s) = if b then 1 else 2 in fun(unit: Unit) => choose[2] true) (())"
      val typed = infer(parse(src))
      assertEquals(pretty.expr(typed),
        "(let choose[s] (b: Bool @ s): Int @ (s | 1 | 1) = if@s b then (fun($s0) => lift[s | 1 | 1]($s0)) 1@1 else" +
        " (fun($s1) => lift[s | 1 | 1]($s1)) 2@1 in (fun($s5) => lift[1](fun($s6) => (fun($s4) => lift[2 | 1 | " +
        "1]($s4)) ($s5 ((fun($s3) => lift[1]($s3)) $s6@1)@1)@1)) (fun(unit: Unit): Int @ (2 | 1 | 1) => choose[2] " +
        "((fun($s2) => lift[2]($s2)) true@1)@1)@1) ((fun($s7) => lift[1]($s7)) (())@1)@1")
      assertEquals(run(s"run($src)"), Value.VNum(1))
    }

    {
      val src =
        "sfun[a, b, c, d: a <= c, b <= c, a <= d, b <= d] => " +
        "fun(x: Int@a) => fun(y: Int@b) => if lift[2](true) then x else y"
      val typed = infer(parse(src))
      assertEquals(pretty.expr(typed),
        "sfun[a] => sfun[b] => sfun[c] => sfun[d: a <= c, b <= c, a <= d, b <= d] => fun(x: Int @ a): Int @ b -> " +
        "Int @ (2 | a | b) => fun(y: Int @ b): Int @ (2 | a | b) => if@2 lift[2](true) then (fun($s0) => lift[2 | " +
        "a | b]($s0)) x@1 else (fun($s1) => lift[2 | a | b]($s1)) y@1")
    }

    {
      val src = "let choose[a, b, c](p: Bool@a)(x: Int@b)(y: Int@c) = if p then x else y in choose[1, 1, 1](false)(3)(4)"
      val typed = infer(parse(src))
      assert(Nil.implyTyEq(typed.ty.get, TInt.at()))
    assertEquals(pretty.expr(typed),
      "let choose[a, b, c] (p: Bool @ a) (x: Int @ b) (y: Int @ c): Int @ b -> Int @ c -> Int @ (a | b | c) = " +
      "if@a p then (fun($s0) => lift[a | b | c]($s0)) x@1 else (fun($s1) => lift[a | b | c]($s1)) y@1 in " +
      "(fun($s5) => lift[1]($s5)) (choose[1, 1, 1] ((fun($s2) => lift[1]($s2)) false@1)@1 ((fun($s3) => " +
      "lift[1]($s3)) 3@1)@1 ((fun($s4) => lift[1]($s4)) 4@1)@1)@1")
      assertEquals(run(src), Value.VNum(4))
    }

    {
      val src = "(let choose[a, b, c] (p: Bool @ a) (x: Int @ b) (y: Int @ c) = if p then x else y in fun(unit: Unit) => choose[1, 1, 2] false 3 4) (())"
      val typed = infer(parse(src))
      assert(Nil.implyTyEq(typed.ty.get, TInt.at(Dyn)))
    assertEquals(pretty.expr(typed),
      "(let choose[a, b, c] (p: Bool @ a) (x: Int @ b) (y: Int @ c): Int @ b -> Int @ c -> Int @ (a | b | c) = " +
      "if@a p then (fun($s0) => lift[a | b | c]($s0)) x@1 else (fun($s1) => lift[a | b | c]($s1)) y@1 in " +
      "(fun($s7) => lift[1](fun($s8) => (fun($s6) => lift[1 | 1 | 2]($s6)) ($s7 ((fun($s5) => lift[1]($s5)) " +
      "$s8@1)@1)@1)) (fun(unit: Unit): Int @ (1 | 1 | 2) => choose[1, 1, 2] ((fun($s2) => lift[1]($s2)) " +
      "false@1)@1 ((fun($s3) => lift[1]($s3)) 3@1)@1 ((fun($s4) => lift[2]($s4)) 4@1)@1)@1) ((fun($s9) => " +
      "lift[1]($s9)) (())@1)@1")
      assertEquals(run(s"run($src)"), Value.VNum(4))
    }

    {
      val src = "(let choose[a, b, c] (p: Bool @ a) (x: Int @ b) (y: Int @ c) = if p then x else y in fun(unit: Unit) => choose[1, 2, 1] false 3 4) (())"
      val typed = infer(parse(src))
      assert(Nil.implyTyEq(typed.ty.get, TInt.at(Dyn)))
    assertEquals(pretty.expr(typed),
      "(let choose[a, b, c] (p: Bool @ a) (x: Int @ b) (y: Int @ c): Int @ b -> Int @ c -> Int @ (a | b | c) = " +
      "if@a p then (fun($s0) => lift[a | b | c]($s0)) x@1 else (fun($s1) => lift[a | b | c]($s1)) y@1 in " +
      "(fun($s7) => lift[1](fun($s8) => (fun($s6) => lift[1 | 2 | 1]($s6)) ($s7 ((fun($s5) => lift[1]($s5)) " +
      "$s8@1)@1)@1)) (fun(unit: Unit): Int @ (1 | 2 | 1) => choose[1, 2, 1] ((fun($s2) => lift[1]($s2)) " +
      "false@1)@1 ((fun($s3) => lift[2]($s3)) 3@1)@1 ((fun($s4) => lift[1]($s4)) 4@1)@1)@1) ((fun($s9) => " +
      "lift[1]($s9)) (())@1)@1")
      assertEquals(run(s"run($src)"), Value.VNum(4))
    }

    {
      val src = "(let choose[a, b, c] (p: Bool @ a) (x: Int @ b) (y: Int @ c) = if p then x else y in fun(unit: Unit) => choose[1, 2, 2] false 3 4) (())"
      val typed = infer(parse(src))
      assert(Nil.implyTyEq(typed.ty.get, TInt.at(Dyn)))
    assertEquals(pretty.expr(typed),
      "(let choose[a, b, c] (p: Bool @ a) (x: Int @ b) (y: Int @ c): Int @ b -> Int @ c -> Int @ (a | b | c) = " +
      "if@a p then (fun($s0) => lift[a | b | c]($s0)) x@1 else (fun($s1) => lift[a | b | c]($s1)) y@1 in " +
      "(fun($s7) => lift[1](fun($s8) => (fun($s6) => lift[1 | 2 | 2]($s6)) ($s7 ((fun($s5) => lift[1]($s5)) " +
      "$s8@1)@1)@1)) (fun(unit: Unit): Int @ (1 | 2 | 2) => choose[1, 2, 2] ((fun($s2) => lift[1]($s2)) " +
      "false@1)@1 ((fun($s3) => lift[2]($s3)) 3@1)@1 ((fun($s4) => lift[2]($s4)) 4@1)@1)@1) ((fun($s9) => " +
      "lift[1]($s9)) (())@1)@1")
      assertEquals(run(s"run($src)"), Value.VNum(4))
    }

    {
      val src = "(let choose[a, b, c] (p: Bool @ a) (x: Int @ b) (y: Int @ c) = if p then x else y in fun(unit: Unit) => choose[2, 1, 1] false 3 4) (())"
      val typed = infer(parse(src))
      assert(Nil.implyTyEq(typed.ty.get, TInt.at(Dyn)))
    assertEquals(pretty.expr(typed),
      "(let choose[a, b, c] (p: Bool @ a) (x: Int @ b) (y: Int @ c): Int @ b -> Int @ c -> Int @ (a | b | c) = " +
      "if@a p then (fun($s0) => lift[a | b | c]($s0)) x@1 else (fun($s1) => lift[a | b | c]($s1)) y@1 in " +
      "(fun($s7) => lift[1](fun($s8) => (fun($s6) => lift[2 | 1 | 1]($s6)) ($s7 ((fun($s5) => lift[1]($s5)) " +
      "$s8@1)@1)@1)) (fun(unit: Unit): Int @ (2 | 1 | 1) => choose[2, 1, 1] ((fun($s2) => lift[2]($s2)) " +
      "false@1)@1 ((fun($s3) => lift[1]($s3)) 3@1)@1 ((fun($s4) => lift[1]($s4)) 4@1)@1)@1) ((fun($s9) => " +
      "lift[1]($s9)) (())@1)@1")
      assertEquals(run(s"run($src)"), Value.VNum(4))
    }

    {
      val src = "(let choose[a, b, c] (p: Bool @ a) (x: Int @ b) (y: Int @ c) = if p then x else y in fun(unit: Unit) => choose[2, 1, 2] false 3 4) (())"
      val typed = infer(parse(src))
      assert(Nil.implyTyEq(typed.ty.get, TInt.at(Dyn)))
    assertEquals(pretty.expr(typed),
      "(let choose[a, b, c] (p: Bool @ a) (x: Int @ b) (y: Int @ c): Int @ b -> Int @ c -> Int @ (a | b | c) = " +
      "if@a p then (fun($s0) => lift[a | b | c]($s0)) x@1 else (fun($s1) => lift[a | b | c]($s1)) y@1 in " +
      "(fun($s7) => lift[1](fun($s8) => (fun($s6) => lift[2 | 1 | 2]($s6)) ($s7 ((fun($s5) => lift[1]($s5)) " +
      "$s8@1)@1)@1)) (fun(unit: Unit): Int @ (2 | 1 | 2) => choose[2, 1, 2] ((fun($s2) => lift[2]($s2)) " +
      "false@1)@1 ((fun($s3) => lift[1]($s3)) 3@1)@1 ((fun($s4) => lift[2]($s4)) 4@1)@1)@1) ((fun($s9) => " +
      "lift[1]($s9)) (())@1)@1")
      assertEquals(run(s"run($src)"), Value.VNum(4))
    }

    {
      val src = "(let choose[a, b, c] (p: Bool @ a) (x: Int @ b) (y: Int @ c) = if p then x else y in fun(unit: Unit) => choose[2, 2, 1] false 3 4) (())"
      val typed = infer(parse(src))
      assert(Nil.implyTyEq(typed.ty.get, TInt.at(Dyn)))
    assertEquals(pretty.expr(typed),
      "(let choose[a, b, c] (p: Bool @ a) (x: Int @ b) (y: Int @ c): Int @ b -> Int @ c -> Int @ (a | b | c) = " +
      "if@a p then (fun($s0) => lift[a | b | c]($s0)) x@1 else (fun($s1) => lift[a | b | c]($s1)) y@1 in " +
      "(fun($s7) => lift[1](fun($s8) => (fun($s6) => lift[2 | 2 | 1]($s6)) ($s7 ((fun($s5) => lift[1]($s5)) " +
      "$s8@1)@1)@1)) (fun(unit: Unit): Int @ (2 | 2 | 1) => choose[2, 2, 1] ((fun($s2) => lift[2]($s2)) " +
      "false@1)@1 ((fun($s3) => lift[2]($s3)) 3@1)@1 ((fun($s4) => lift[1]($s4)) 4@1)@1)@1) ((fun($s9) => " +
      "lift[1]($s9)) (())@1)@1")
      assertEquals(run(s"run($src)"), Value.VNum(4))
    }

    {
      val src = "(let choose[a, b, c] (p: Bool @ a) (x: Int @ b) (y: Int @ c) = if p then x else y in fun(unit: Unit) => choose[2, 2, 2] false 3 4) (())"
      val typed = infer(parse(src))
      assert(Nil.implyTyEq(typed.ty.get, TInt.at(Dyn)))
    assertEquals(pretty.expr(typed),
      "(let choose[a, b, c] (p: Bool @ a) (x: Int @ b) (y: Int @ c): Int @ b -> Int @ c -> Int @ (a | b | c) = " +
      "if@a p then (fun($s0) => lift[a | b | c]($s0)) x@1 else (fun($s1) => lift[a | b | c]($s1)) y@1 in " +
      "(fun($s7) => lift[1](fun($s8) => (fun($s6) => lift[2 | 2 | 2]($s6)) ($s7 ((fun($s5) => lift[1]($s5)) " +
      "$s8@1)@1)@1)) (fun(unit: Unit): Int @ (2 | 2 | 2) => choose[2, 2, 2] ((fun($s2) => lift[2]($s2)) " +
      "false@1)@1 ((fun($s3) => lift[2]($s3)) 3@1)@1 ((fun($s4) => lift[2]($s4)) 4@1)@1)@1) ((fun($s9) => " +
      "lift[1]($s9)) (())@1)@1")
      assertEquals(run(s"run($src)"), Value.VNum(4))
    }

    {
      val str = """
        if lift[2](true) then 1 else 2
      """
      val checked = infer(parse(s"(($str): Code[Int])"))
      assertEquals(pretty.expr(checked),
        "(fun($s2) => lift[2]($s2)) (if@2 lift[2](true) then (fun($s0) => lift[2 | 1 | 1]($s0)) 1@1 else (fun($s1)" +
        " => lift[2 | 1 | 1]($s1)) 2@1)@1")
    }
  }

  test("constrained promotion from stage 1 to stage 1") {
    val src = "let promote[a, b: a <= b](x: Int@a) = lift[b](x) in promote[1, 1](3)"
    val typed = infer(parse(src))
    assertEquals(pretty.expr(typed),
      "let promote[a, b: a <= b] (x: Int @ a): Int @ b = lift[b](x) in (fun($s1) => lift[1]($s1)) (promote[1, 1]" +
      " ((fun($s0) => lift[1]($s0)) 3@1)@1)@1")
    assertEquals(run(src), Value.VNum(3))
  }

  test("constrained promotion from stage 1 to stage 2") {
    val src = "(let promote[a, b: a <= b] (x: Int @ a) = lift[b](x) in fun(unit: Unit) => promote[1, 2] 3) (())"
    val typed = infer(parse(src))
    assertEquals(pretty.expr(typed),
      "(let promote[a, b: a <= b] (x: Int @ a): Int @ b = lift[b](x) in (fun($s3) => lift[1](fun($s4) => " +
      "(fun($s2) => lift[2]($s2)) ($s3 ((fun($s1) => lift[1]($s1)) $s4@1)@1)@1)) (fun(unit: Unit): Int @ 2 => " +
      "promote[1, 2] ((fun($s0) => lift[1]($s0)) 3@1)@1)@1) ((fun($s5) => lift[1]($s5)) (())@1)@1")
    assertEquals(run(s"run($src)"), Value.VNum(3))
  }

  test("constrained promotion from stage 2 to stage 2") {
    val src = "(let promote[a, b: a <= b] (x: Int @ a) = lift[b](x) in fun(unit: Unit) => promote[2, 2] 3) (())"
    val typed = infer(parse(src))
    assertEquals(pretty.expr(typed),
      "(let promote[a, b: a <= b] (x: Int @ a): Int @ b = lift[b](x) in (fun($s3) => lift[1](fun($s4) => " +
      "(fun($s2) => lift[2]($s2)) ($s3 ((fun($s1) => lift[1]($s1)) $s4@1)@1)@1)) (fun(unit: Unit): Int @ 2 => " +
      "promote[2, 2] ((fun($s0) => lift[2]($s0)) 3@1)@1)@1) ((fun($s5) => lift[1]($s5)) (())@1)@1")
    assertEquals(run(s"run($src)"), Value.VNum(3))
  }

  test("stage joins retain their syntax under transitive constraints") {
    val src = "sfun[a, b, c: a <= b, b <= c] => fun(x: Int@a) => fun(y: Int@c) => x + y"
    assertEquals(pretty.expr(infer(parse(src))),
      "sfun[a] => sfun[b] => sfun[c: a <= b, b <= c] => fun(x: Int @ a): Int @ c -> Int @ (a | c) => fun(y: Int " +
      "@ c): Int @ (a | c) => (fun($s0) => lift[a | c]($s0)) x@1 +@(a | c) (fun($s1) => lift[a | c]($s1)) y@1")
    val program = s"run(($src)[1, 1, 2](3)(4))"
    assertEquals(run(program), Value.VNum(7))

    val bounded = infer(parse("sfun[s: 2 <= s] => fun(x: Int@s) => x + lift[2](1)"))
    assertEquals(pretty.expr(bounded),
      "sfun[s: 2 <= s] => fun(x: Int @ s): Int @ (s | 2) => (fun($s0) => lift[s | 2]($s0)) x@1 +@(s | 2) " +
      "(fun($s1) => lift[s | 2]($s1)) (lift[2](1))@1")
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
      "sfun[s: 2 <= s] => fun(x: Int @ s): forall[$s0: $s0 <= 1]. Int @ $s0 -> Int @ (s | $s0) => sfun[$s0: $s0 " +
      "<= 1] => fun(y: Int @ $s0): Int @ (s | $s0) => (fun($s1) => lift[s | $s0]($s1)) x@1 +@(s | $s0) (fun($s2)" +
      " => lift[s | $s0]($s2)) y@1")
    assertEquals(run(s"run(($src)[2](3)[1](4))"), Value.VNum(7))
  }

  test("joined stage application instantiated at [1, 1]") {
    val src = "let id[s](x: Int@s) = x in let use[a, b](x: Int@(a | b)) = id[a | b](x) in use[1, 1](3)"
    val typed = infer(parse(src))
    assertEquals(pretty.expr(typed),
      "let id[s] (x: Int @ s): Int @ s = x in (fun($s3) => lift[1]($s3)) (let use[a, b] (x: Int @ (a | b)): Int " +
      "@ (a | b) = id[a | b] ((fun($s0) => lift[a | b]($s0)) x@1)@1 in (fun($s2) => lift[1]($s2)) (use[1, 1] " +
      "((fun($s1) => lift[1 | 1]($s1)) 3@1)@1)@1)@1")
    assertEquals(run(src), Value.VNum(3))
  }

  test("joined stage application instantiated at [1, 2]") {
    val src = "(let id[s] (x: Int @ s) = x in let use[a, b] (x: Int @ (a | b)) = id[a | b] x in fun(unit: Unit) => use[1, 2] 3) (())"
    val typed = infer(parse(src))
    assertEquals(pretty.expr(typed),
      "(let id[s] (x: Int @ s): Int @ s = x in (fun($s8) => lift[1](fun($s9) => (fun($s7) => lift[1 | 2]($s7)) " +
      "($s8 ((fun($s6) => lift[1]($s6)) $s9@1)@1)@1)) (let use[a, b] (x: Int @ (a | b)): Int @ (a | b) = id[a | " +
      "b] ((fun($s0) => lift[a | b]($s0)) x@1)@1 in (fun($s4) => lift[1](fun($s5) => (fun($s3) => lift[1 | " +
      "2]($s3)) ($s4 ((fun($s2) => lift[1]($s2)) $s5@1)@1)@1)) (fun(unit: Unit): Int @ (1 | 2) => use[1, 2] " +
      "((fun($s1) => lift[1 | 2]($s1)) 3@1)@1)@1)@1) ((fun($s10) => lift[1]($s10)) (())@1)@1")
    assertEquals(run(s"run($src)"), Value.VNum(3))
  }

  test("joined constraint accepts [1, 2]") {
    val src = "let force[a, b: 2 <= a | b] = 1 in force[1, 2]"
    val typed = infer(parse(src))
    assertEquals(pretty.expr(typed),
      "let force[a, b: 2 <= a | b] = 1 in (fun($s0) => lift[1]($s0)) (force[1, 2])@1")
    assertEquals(run(src), Value.VNum(1))
  }

  test("joined constraint accepts [2, 1]") {
    val src = "let force[a, b: 2 <= a | b] = 1 in force[2, 1]"
    val typed = infer(parse(src))
    assertEquals(pretty.expr(typed),
      "let force[a, b: 2 <= a | b] = 1 in (fun($s0) => lift[1]($s0)) (force[2, 1])@1")
    assertEquals(run(src), Value.VNum(1))
  }

  test("joined constraint accepts [2, 2]") {
    val src = "let force[a, b: 2 <= a | b] = 1 in force[2, 2]"
    val typed = infer(parse(src))
    assertEquals(pretty.expr(typed),
      "let force[a, b: 2 <= a | b] = 1 in (fun($s0) => lift[1]($s0)) (force[2, 2])@1")
    assertEquals(run(src), Value.VNum(1))
  }

  test("join constraints compose transitively") {
    val src = "sfun[a, b, c, d: a <= b | c, b <= d, c <= d] => fun(x: Int@a) => lift[d](x)"
    val typed = infer(parse(src))
    assertEquals(pretty.expr(typed),
      "sfun[a] => sfun[b] => sfun[c] => sfun[d: a <= b | c, b <= d, c <= d] => fun(x: Int @ a): Int @ d => " +
      "lift[d](x)")
  }

  test("reference stage join instantiated at [1, 1]") {
    val src =
      "let use[a, b] = let cell = ref@(a | b)(lift[a | b](1)) in let ignored = cell :=@(b | a) lift[a | b](2) in " +
      "!@(b | a) cell in use[1, 1]"
    val typed = infer(parse(src))
    assertEquals(pretty.expr(typed),
      "let use[a, b] = let cell = ref@(a | b)(lift[a | b](1)) in (fun($s2) => lift[a | b]($s2)) (let ignored = " +
      "cell :=@(b | a) (fun($s0) => lift[b | a]($s0)) (lift[a | b](2))@1 in (fun($s1) => lift[b | a]($s1)) (!@(b" +
      " | a) cell)@1)@1 in (fun($s3) => lift[1]($s3)) (use[1, 1])@1")
    assertEquals(run(src), Value.VNum(2))
  }

  test("reference stage join instantiated at [1, 2]") {
    val src =
      "(let use[a, b] = let cell = ref@(a | b)(lift[a | b](1)) in let ignored = cell :=@(b | a) lift[a | b](2) in " +
      "!@(b | a) cell in fun(unit: Unit) => use[1, 2])(())"
    val typed = infer(parse(src))
    assertEquals(pretty.expr(typed),
      "(let use[a, b] = let cell = ref@(a | b)(lift[a | b](1)) in (fun($s2) => lift[a | b]($s2)) (let ignored = " +
      "cell :=@(b | a) (fun($s0) => lift[b | a]($s0)) (lift[a | b](2))@1 in (fun($s1) => lift[b | a]($s1)) (!@(b" +
      " | a) cell)@1)@1 in (fun($s5) => lift[1](fun($s6) => (fun($s4) => lift[1 | 2]($s4)) ($s5 ((fun($s3) => " +
      "lift[1]($s3)) $s6@1)@1)@1)) (fun(unit: Unit): Int @ (1 | 2) => use[1, 2])@1) ((fun($s7) => lift[1]($s7)) " +
      "(())@1)@1")
    assertEquals(run(s"run($src)"), Value.VNum(2))
  }

  test("reference stage join instantiated at [2, 1]") {
    val src =
      "(let use[a, b] = let cell = ref@(a | b)(lift[a | b](1)) in let ignored = cell :=@(b | a) lift[a | b](2) in " +
      "!@(b | a) cell in fun(unit: Unit) => use[2, 1])(())"
    val typed = infer(parse(src))
    assertEquals(pretty.expr(typed),
      "(let use[a, b] = let cell = ref@(a | b)(lift[a | b](1)) in (fun($s2) => lift[a | b]($s2)) (let ignored = " +
      "cell :=@(b | a) (fun($s0) => lift[b | a]($s0)) (lift[a | b](2))@1 in (fun($s1) => lift[b | a]($s1)) (!@(b" +
      " | a) cell)@1)@1 in (fun($s5) => lift[1](fun($s6) => (fun($s4) => lift[2 | 1]($s4)) ($s5 ((fun($s3) => " +
      "lift[1]($s3)) $s6@1)@1)@1)) (fun(unit: Unit): Int @ (2 | 1) => use[2, 1])@1) ((fun($s7) => lift[1]($s7)) " +
      "(())@1)@1")
    assertEquals(run(s"run($src)"), Value.VNum(2))
  }

  test("reference stage join instantiated at [2, 2]") {
    val src =
      "(let use[a, b] = let cell = ref@(a | b)(lift[a | b](1)) in let ignored = cell :=@(b | a) lift[a | b](2) in " +
      "!@(b | a) cell in fun(unit: Unit) => use[2, 2])(())"
    val typed = infer(parse(src))
    assertEquals(pretty.expr(typed),
      "(let use[a, b] = let cell = ref@(a | b)(lift[a | b](1)) in (fun($s2) => lift[a | b]($s2)) (let ignored = " +
      "cell :=@(b | a) (fun($s0) => lift[b | a]($s0)) (lift[a | b](2))@1 in (fun($s1) => lift[b | a]($s1)) (!@(b" +
      " | a) cell)@1)@1 in (fun($s5) => lift[1](fun($s6) => (fun($s4) => lift[2 | 2]($s4)) ($s5 ((fun($s3) => " +
      "lift[1]($s3)) $s6@1)@1)@1)) (fun(unit: Unit): Int @ (2 | 2) => use[2, 2])@1) ((fun($s7) => lift[1]($s7)) " +
      "(())@1)@1")
    assertEquals(run(s"run($src)"), Value.VNum(2))
  }

  test("function subtyping coerces arguments contravariantly and results covariantly") {
    val src = "fun(x: Code[Int]): Int => 7"
    val expected = TFun(TInt, TInt.at(Dyn))
    val typed = infer(parse(s"(($src): Int -> Code[Int])"))
    assertEquals(pretty.expr(typed),
      "(fun($s3) => lift[1](fun($s4) => (fun($s2) => lift[2]($s2)) ($s3 ((fun($s1) => lift[2]($s1)) " +
      "$s4@1)@1)@1)) (fun(x: Int @ 2): Int => (fun($s0) => lift[1]($s0)) 7@1)@1")
    assert(Nil.implyTyEq(typed.ty.get, expected.at()))
    assertEquals(instar.interp.eval(ERun(EApp(typed, ENum(3), Some(Sta))))._1,
      Value.VNum(7))
    val lifted = infer(parse(s"(($src): Code[Int -> Int])"))
    assertEquals(pretty.expr(lifted),
      "(fun($s3) => fun@2($s4) => (fun($s2) => lift[2]($s2)) ($s3 ((fun($s1) => lift[2]($s1)) $s4@1)@1)@1) " +
      "(fun(x: Int @ 2): Int => (fun($s0) => lift[1]($s0)) 7@1)@1")
    assertEquals(instar.interp.eval(ERun(EApp(lifted, ELift(ENum(3), Dyn), Some(Dyn))))._1,
      Value.VNum(7))
  }

  test("fresh names restart for each program and remain distinct within a program") {
    val src = """
      let f: Int -> Code[Int] = fun(x: Code[Int]): Int => 1 in
      let g: Int -> Code[Int] = fun(y: Code[Int]): Int => 2 in g
    """
    val expected =
      "let f = (fun($s3) => lift[1](fun($s4) => (fun($s2) => lift[2]($s2)) ($s3 ((fun($s1) => lift[2]($s1)) " +
      "$s4@1)@1)@1)) (fun(x: Int @ 2): Int => (fun($s0) => lift[1]($s0)) 1@1)@1 in (fun($s16) => " +
      "lift[1](fun($s17) => (fun($s15) => lift[2]($s15)) ($s16 ((fun($s14) => lift[1]($s14)) $s17@1)@1)@1)) (let" +
      " g = (fun($s8) => lift[1](fun($s9) => (fun($s7) => lift[2]($s7)) ($s8 ((fun($s6) => lift[2]($s6)) " +
      "$s9@1)@1)@1)) (fun(y: Int @ 2): Int => (fun($s5) => lift[1]($s5)) 2@1)@1 in (fun($s12) => " +
      "lift[1](fun($s13) => (fun($s11) => lift[2]($s11)) ($s12 ((fun($s10) => lift[1]($s10)) $s13@1)@1)@1)) " +
      "g@1)@1"

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
      "let cell = ref@1(0) in (fun($s29) => lift[1]($s29)) (let make = (fun($s16) => lift[1](fun($s17) => " +
      "(fun($s14) => lift[1](fun($s15) => (fun($s13) => lift[1]($s13)) ($s14 ((fun($s12) => lift[1]($s12)) " +
      "$s15@1)@1)@1)) ($s16 ((fun($s11) => lift[1]($s11)) $s17@1)@1)@1)) (fun(u: Unit): Int -> Int => (fun($s9) " +
      "=> lift[1](fun($s10) => (fun($s8) => lift[1]($s8)) ($s9 ((fun($s7) => lift[1]($s7)) $s10@1)@1)@1)) (let " +
      "ignored = cell :=@1 (fun($s2) => lift[1]($s2)) ((fun($s0) => lift[1 | 1]($s0)) (!@1 cell)@1 +@(1 | 1) " +
      "(fun($s1) => lift[1 | 1]($s1)) 1@1)@1 in (fun($s5) => lift[1](fun($s6) => (fun($s4) => lift[1]($s4)) ($s5" +
      " ((fun($s3) => lift[1]($s3)) $s6@1)@1)@1)) (fun(x: Int): Int => x)@1)@1)@1 in (fun($s28) => " +
      "lift[1]($s28)) (let f = (fun($s21) => lift[1](fun($s22) => (fun($s20) => lift[2]($s20)) ($s21 ((fun($s19)" +
      " => lift[1]($s19)) $s22@1)@1)@1)) (make ((fun($s18) => lift[1]($s18)) (())@1)@1)@1 in (fun($s27) => " +
      "lift[1]($s27)) ((fun(first: Int @ 2): Int => (fun(second: Int @ 2): Int => !@1 cell) ((fun($s24) => " +
      "lift[2]($s24)) (f ((fun($s23) => lift[1]($s23)) 2@1)@1)@1)@1) ((fun($s26) => lift[2]($s26)) (f " +
      "((fun($s25) => lift[1]($s25)) 1@1)@1)@1)@1)@1)@1)@1")
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
      "(run(fun@2(x: Int @ 2): Int @ 2 => x)) ((fun($s0) => lift[1]($s0)) 3@1)@1")
    assertEquals(run(direct), Value.VNum(3))
    val staged = "run((sfun[s] => fun@s(x: Code[Int]) => x)[2])(3)"
    val typed = infer(parse(staged))
    assertEquals(pretty.expr(typed),
      "(run((sfun[s] => fun@s(x: Int @ 2): Int @ 2 => x)[2])) ((fun($s0) => lift[1]($s0)) 3@1)@1")
    assert(Nil.implyTyEq(typed.ty.get, TInt.at()))
    assertEquals(run(staged), Value.VNum(3))
    val joined = "run((lift[2](1): Int@(1 | 2)))"
    assertEquals(pretty.expr(infer(parse(joined))),
      "run((fun($s0) => lift[1 | 2]($s0)) (lift[2](1))@1)")
    assertEquals(run(joined), Value.VNum(1))
  }

  test("stage binders shadow without capturing outer stages or constraints") {
    val src = "sfun[s] => sfun[s: 2 <= s] => fun(x: Int@s) => x + 1"
    assertEquals(pretty.expr(infer(parse(src))),
      "sfun[s] => sfun[$s0: 2 <= $s0] => fun(x: Int @ $s0): Int @ ($s0 | 1) => (fun($s1) => lift[$s0 | 1]($s1)) " +
      "x@1 +@($s0 | 1) (fun($s2) => lift[$s0 | 1]($s2)) 1@1")
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
      "letrec@1 f = lift[1](fun($s11: Int): Int => (fun($s9) => lift[1](fun($s10) => (fun($s8) => lift[1]($s8)) " +
      "($s9 ((fun($s7) => lift[1]($s7)) $s10@1)@1)@1)) (fun(n: Int): Int @ (1 | 1 | 1 | 1) => if@(1 | 1) " +
      "(fun($s0) => lift[1 | 1]($s0)) n@1 <=@(1 | 1) (fun($s1) => lift[1 | 1]($s1)) 0@1 then (fun($s5) => lift[1" +
      " | 1 | 1 | 1]($s5)) 1@1 else (fun($s6) => lift[1 | 1 | 1 | 1]($s6)) (f ((fun($s4) => lift[1]($s4)) " +
      "((fun($s2) => lift[1 | 1]($s2)) n@1 -@(1 | 1) (fun($s3) => lift[1 | 1]($s3)) 1@1)@1)@1)@1)@1 $s11@1) in " +
      "(fun($s14) => lift[1](fun($s15) => (fun($s13) => lift[1]($s13)) ($s14 ((fun($s12) => lift[1]($s12)) " +
      "$s15@1)@1)@1)) f@1")
    assertEquals(run(s"($static)(3)"), Value.VNum(1))
    assertEquals(pretty.expr(infer(parse("fix@(1 | 1) f: Int -> Int. fun(n: Int) => n"))),
      "letrec@1 f = lift[1](fun($s4: Int): Int => (fun($s2) => lift[1](fun($s3) => (fun($s1) => lift[1]($s1)) " +
      "($s2 ((fun($s0) => lift[1]($s0)) $s3@1)@1)@1)) (fun(n: Int): Int => n)@1 $s4@1) in (fun($s7) => " +
      "lift[1](fun($s8) => (fun($s6) => lift[1]($s6)) ($s7 ((fun($s5) => lift[1]($s5)) $s8@1)@1)@1)) f@1")
    val dynamic = "fix f: Code[Int -> Int]. fun@2(n: Code[Int]) => if n <= 0 then 1 else f(n - 1)"
    assertEquals(pretty.expr(infer(parse(dynamic))),
      "letrec@2 f = fun@2($s11: Int @ 2): Int @ 2 => (fun($s9) => fun@2($s10) => (fun($s8) => lift[2]($s8)) ($s9" +
      " ((fun($s7) => lift[2]($s7)) $s10@1)@2)@1) (fun@2(n: Int @ 2): Int @ (2 | 1 | 1 | 2) => if@(2 | 1) " +
      "(fun($s0) => lift[2 | 1]($s0)) n@1 <=@(2 | 1) (fun($s1) => lift[2 | 1]($s1)) 0@1 then (fun($s5) => lift[2" +
      " | 1 | 1 | 2]($s5)) 1@1 else (fun($s6) => lift[2 | 1 | 1 | 2]($s6)) (f ((fun($s4) => lift[2]($s4)) " +
      "((fun($s2) => lift[2 | 1]($s2)) n@1 -@(2 | 1) (fun($s3) => lift[2 | 1]($s3)) 1@1)@1)@2)@1)@1 $s11@2 in " +
      "(fun($s14) => fun@2($s15) => (fun($s13) => lift[2]($s13)) ($s14 ((fun($s12) => lift[2]($s12)) " +
      "$s15@1)@2)@1) f@1")
    assertEquals(run(s"run(($dynamic)(3))"), Value.VNum(1))
  }

  test("fix preserves a symbolic outer stage") {
    val src = "sfun[s] => fix@s f: (Int@s -> Int@s)@s. " +
      "fun@s(n: Int@s) => if n <= 0 then 1 else f(n - 1)"
    assertEquals(pretty.expr(infer(parse(src))),
      "sfun[s] => letrec@s f = fun@s($s11: Int @ s): Int @ s => (fun($s9) => fun@s($s10) => (fun($s8) => " +
      "lift[s]($s8)) ($s9 ((fun($s7) => lift[s]($s7)) $s10@1)@s)@1) (fun@s(n: Int @ s): Int @ (s | 1 | 1 | s) =>" +
      " if@(s | 1) (fun($s0) => lift[s | 1]($s0)) n@1 <=@(s | 1) (fun($s1) => lift[s | 1]($s1)) 0@1 then " +
      "(fun($s5) => lift[s | 1 | 1 | s]($s5)) 1@1 else (fun($s6) => lift[s | 1 | 1 | s]($s6)) (f ((fun($s4) => " +
      "lift[s]($s4)) ((fun($s2) => lift[s | 1]($s2)) n@1 -@(s | 1) (fun($s3) => lift[s | 1]($s3)) " +
      "1@1)@1)@s)@1)@1 $s11@s in (fun($s14) => fun@s($s15) => (fun($s13) => lift[s]($s13)) ($s14 ((fun($s12) => " +
      "lift[s]($s12)) $s15@1)@s)@1) f@1")
    assertEquals(run(s"($src)[1](3)"), Value.VNum(1))
    assertEquals(run(s"run(($src)[2](lift[2](3)))"), Value.VNum(1))
  }

  test("fix preserves a joined outer stage") {
    val src = "sfun[a, b] => fix f: (Int@(a | b) -> Int@(a | b))@(a | b). " +
      "fun@(a | b)(x: Int@(a | b)) => x"
    assertEquals(pretty.expr(infer(parse(src))),
      "sfun[a, b] => letrec@(a | b) f = fun@(a | b)($s4: Int @ (a | b)): Int @ (a | b) => (fun($s2) => fun@(a | " +
      "b)($s3) => (fun($s1) => lift[a | b]($s1)) ($s2 ((fun($s0) => lift[a | b]($s0)) $s3@1)@(a | b))@1) (fun@(a" +
      " | b)(x: Int @ (a | b)): Int @ (a | b) => x)@1 $s4@(a | b) in (fun($s7) => fun@(a | b)($s8) => (fun($s6) " +
      "=> lift[a | b]($s6)) ($s7 ((fun($s5) => lift[a | b]($s5)) $s8@1)@(a | b))@1) f@1")
    assertEquals(run(s"($src)[1, 1](7)"), Value.VNum(7))
    assertEquals(run(s"run(($src)[1, 2](lift[2](7)))"), Value.VNum(7))
  }

  test("fix supports annotated polymorphic recursion") {
    val src = "fix f: forall[s]. Int -> Int@s. sfun[s] => fun(n: Int) => " +
      "if n <= 0 then lift[s](1) else f[s](n - 1)"
    assertEquals(pretty.expr(infer(parse(src))),
      "letrec@1 f[$s9] = ((fun($s8) => $s8) (sfun[s] => fun(n: Int): Int @ (1 | 1 | s | s) => if@(1 | 1) " +
      "(fun($s0) => lift[1 | 1]($s0)) n@1 <=@(1 | 1) (fun($s1) => lift[1 | 1]($s1)) 0@1 then (fun($s5) => lift[1" +
      " | 1 | s | s]($s5)) (lift[s](1))@1 else (fun($s6) => lift[1 | 1 | s | s]($s6)) (f[s] ((fun($s4) => " +
      "lift[1]($s4)) ((fun($s2) => lift[1 | 1]($s2)) n@1 -@(1 | 1) (fun($s3) => lift[1 | 1]($s3)) " +
      "1@1)@1)@1)@1)@1)[$s9] in (fun($s11) => $s11) f@1")
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
        "let cell = ref@1(0) in (fun($s26) => lift[1]($s26)) (let f = letrec@1 f = lift[1](fun($s11: Int): Int => " +
        "(fun($s9) => lift[1](fun($s10) => (fun($s8) => lift[1]($s8)) ($s9 ((fun($s7) => lift[1]($s7)) " +
        "$s10@1)@1)@1)) (let ignored = cell :=@1 (fun($s2) => lift[1]($s2)) ((fun($s0) => lift[1 | 1]($s0)) (!@1 " +
        "cell)@1 +@(1 | 1) (fun($s1) => lift[1 | 1]($s1)) 1@1)@1 in (fun($s5) => lift[1](fun($s6) => (fun($s4) => " +
        "lift[1]($s4)) ($s5 ((fun($s3) => lift[1]($s3)) $s6@1)@1)@1)) (fun(n: Int): Int => n)@1)@1 $s11@1) in " +
        "(fun($s14) => lift[1](fun($s15) => (fun($s13) => lift[1]($s13)) ($s14 ((fun($s12) => lift[1]($s12)) " +
        "$s15@1)@1)@1)) f@1 in (fun($s25) => lift[1]($s25)) (let before = !@1 cell in (fun($s24) => lift[1]($s24))" +
        " (let first = f ((fun($s16) => lift[1]($s16)) 1@1)@1 in (fun($s23) => lift[1]($s23)) (let second = f " +
        "((fun($s17) => lift[1]($s17)) 2@1)@1 in (fun($s22) => lift[1]($s22)) ((fun($s20) => lift[1 | 1 | " +
        "1]($s20)) ((fun($s18) => lift[1 | 1]($s18)) before@1 *@(1 | 1) (fun($s19) => lift[1 | 1]($s19)) 100@1)@1 " +
        "+@(1 | 1 | 1) (fun($s21) => lift[1 | 1 | 1]($s21)) (!@1 cell)@1)@1)@1)@1)@1)@1")
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
        "let cell = ref@2(lift[2](0)) in (fun($s22) => lift[2]($s22)) (letrec@2 f = fun@2($s11: Int @ 2): Int @ 2 " +
        "=> (fun($s9) => fun@2($s10) => (fun($s8) => lift[2]($s8)) ($s9 ((fun($s7) => lift[2]($s7)) $s10@1)@2)@1) " +
        "(let ignored = cell :=@2 (fun($s2) => lift[2]($s2)) ((fun($s0) => lift[2 | 1]($s0)) (!@2 cell)@1 +@(2 | " +
        "1) (fun($s1) => lift[2 | 1]($s1)) 1@1)@1 in (fun($s5) => fun@2($s6) => (fun($s4) => lift[2]($s4)) ($s5 " +
        "((fun($s3) => lift[2]($s3)) $s6@1)@2)@1) (fun@2(n: Int @ 2): Int @ 2 => n)@1)@1 $s11@2 in (fun($s21) => " +
        "lift[2]($s21)) (let before = !@2 cell in (fun($s20) => lift[2]($s20)) (let first = f ((fun($s12) => " +
        "lift[2]($s12)) 1@1)@2 in (fun($s19) => lift[2]($s19)) (let second = f ((fun($s13) => lift[2]($s13)) " +
        "2@1)@2 in (fun($s18) => lift[2]($s18)) ((fun($s16) => lift[2 | 1 | 2]($s16)) ((fun($s14) => lift[2 | " +
        "1]($s14)) before@1 *@(2 | 1) (fun($s15) => lift[2 | 1]($s15)) 100@1)@1 +@(2 | 1 | 2) (fun($s17) => lift[2" +
        " | 1 | 2]($s17)) (!@2 cell)@1)@1)@1)@1)@1)@1")
      assertEquals(run(s"run($src)"), Value.VNum(2))
    }
  }

  test("fix delays a computed polymorphic body until stage instantiation") {
    {
      val src = "fix f: forall[s]. Int@s -> Int@s. " +
        "if true then sfun[s] => fun(x: Int@s) => x else f"
      assertEquals(pretty.expr(infer(parse(src))),
        "letrec@1 f[$s7] = ((fun($s6) => $s6) (if@1 true then (fun($s2) => $s2) (sfun[s] => fun(x: Int @ s): Int @" +
        " s => x)@1 else (fun($s4) => $s4) f@1)@1)[$s7] in (fun($s9) => $s9) f@1")
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
        "let cell = ref@1(0) in (fun($s16) => lift[1]($s16)) (letrec@1 f[$s7] = ((fun($s6) => $s6) (let ignored = " +
        "cell :=@1 (fun($s2) => lift[1]($s2)) ((fun($s0) => lift[1 | 1]($s0)) (!@1 cell)@1 +@(1 | 1) (fun($s1) => " +
        "lift[1 | 1]($s1)) 1@1)@1 in (fun($s4) => $s4) (sfun[s] => 1)@1)@1)[$s7] in (fun($s15) => lift[1]($s15)) " +
        "(let before = !@1 cell in (fun($s14) => lift[1]($s14)) (let first = f[1] in (fun($s13) => lift[1]($s13)) " +
        "(let second = f[2] in (fun($s12) => lift[1]($s12)) ((fun($s10) => lift[1 | 1 | 1]($s10)) ((fun($s8) => " +
        "lift[1 | 1]($s8)) before@1 *@(1 | 1) (fun($s9) => lift[1 | 1]($s9)) 100@1)@1 +@(1 | 1 | 1) (fun($s11) => " +
        "lift[1 | 1 | 1]($s11)) (!@1 cell)@1)@1)@1)@1)@1)@1")
      assertEquals(run(src), Value.VNum(2))
    }
  }

  test("coerce primitives") {
    {
      val expr = parse("fun(x: Int): Int@2 => 1")
      val inferred = infer(expr)
      assertEquals(pretty.expr(inferred),
        "fun(x: Int): Int @ 2 => (fun($s0) => lift[2]($s0)) 1@1")
    }
    {
      val expr = parse("fun(x: Int): Unit@2 => ()")
      val inferred = infer(expr)
      assertEquals(pretty.expr(inferred),
        "fun(x: Int): Unit @ 2 => (fun($s0) => lift[2]($s0)) (())@1")
    }
    {
      val expr = parse("fun(x: Int): Bool@2 => true")
      val inferred = infer(expr)
      assertEquals(pretty.expr(inferred),
        "fun(x: Int): Bool @ 2 => (fun($s0) => lift[2]($s0)) true@1")
    }
  }

  test("coerce var") {
    {
      val expr = parse("fun(x: Int): Int@2 => x")
      val inferred = infer(expr)
      assertEquals(pretty.expr(inferred),
        "fun(x: Int): Int @ 2 => (fun($s0) => lift[2]($s0)) x@1")
    }
    {
      val expr = parse("sfun[s] => fun(x: Int): Int@s => x")
      val inferred = infer(expr)
      assertEquals(pretty.expr(inferred),
        "sfun[s] => fun(x: Int): Int @ s => (fun($s0) => lift[s]($s0)) x@1")
    }
  }

class ElabNegativeTest extends FunSuite:
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
