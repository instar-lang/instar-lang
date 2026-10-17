package instar.typing

import munit.IgnoreSuite
import munit.FunSuite

import instar.Config
import instar.pretty
import StageConstraints.*
import instar.parser.parse
import instar.syntax.*
import instar.syntax.given
import Expr.*
import Stage.*
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
      assert(checked.ty == Some(TFun(TInt.at(Dyn), TInt.at(Dyn)).at(Dyn)))
    }
    {
      val str = """
        let f[s1] [s2] = fun@s1(x: Int @ s2) => x in
        f[1][1]
      """
      val checked = infer(parse(str))
      assertEquals(checked.ty, Some(TFun(TInt, TInt)))
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

  test("quantified constraints are compared up to alpha-renaming and entailment") {
    val ty = instar.parser.parseType("forall[s: 1 <= s, s <= 2]. Int@s")
    val expected = instar.parser.parseType("forall[t]. Int@t")
    assert(Nil.implyTyEq(ty, expected))
    assert(!Nil.implyTyEq(instar.parser.parseType("forall[s: 2 <= s]. Int@s"), expected))
  }

  test("join constraints compose transitively") {
    val src = "sfun[a, b, c, d: a <= b | c, b <= d, c <= d] => fun(x: Int@a) => lift[d](x)"
    val typed = infer(parse(src))
    assertEquals(pretty.expr(typed),
      "sfun[a] => sfun[b] => sfun[c] => sfun[d: a <= b | c, b <= d, c <= d] => fun(x: Int @ a): Int @ d => " +
      "lift[d](x)")
  }

  test("stage-poly function") {
    val str1 = """
      let f[s] = fun@s(x: Int @ s) => x in
      let g[s] = f[s] in
      g[2]
    """
    val checked1 = infer(parse(str1))
    assertEquals(checked1.ty, Some(TFun(TInt.at(Dyn), TInt.at(Dyn)).at(Dyn)))

    val str2 = """
      let f[s] = fun@s(x: Int @ s) => x in
      let g[s] = f[s] in
      g[1]
    """
    val checked2 = infer(parse(str2))
    assert(Nil.implyTyEq(checked2.ty.get, TFun(TInt, TInt)))
  }

  test("infer resolves omitted first-stage markers") {
    val typed = infer(parse("let inc = fun(x: Int): Int => x + 1 in inc(41)"))

    assertEquals(typed.ty, Some(TInt))

    val let = typed.asInstanceOf[ELet]
    val lam = let.rhs.asInstanceOf[ELam]
    val plus = lam.body.asInstanceOf[EBinOp]
    val app = let.body.asInstanceOf[EApp]

    assertEquals(lam.ty, Some(TFun(TInt, TInt)))
    assertEquals(plus.st, Some(Sta))
    assertEquals(plus.ty, Some(TInt))
    assertEquals(app.st, Some(Sta))
    assertEquals(app.ty, Some(TInt))
  }

  test("check fills in the lambda result type") {
    val checked = check(parse("fun(x: Int) => x"), TFun(TInt, TInt))

    val lam = checked.asInstanceOf[ELam]
    assertEquals(checked.ty, Some(TFun(TInt, TInt)))
    assertEquals(lam.argTy, Some(TInt))
    assertEquals(lam.retTy, Some(TInt))
    assertEquals(lam.body.ty, Some(TInt))
  }

  test("infer instantiates stage-polymorphic expressions") {
    val typed = infer(parse("(sfun[s] => lift[s](fun(x: Int @ s): Int @ s => x))[2]"))
    assertEquals(typed.ty, Some(TFun(TInt.at(Dyn), TInt.at(Dyn)).at(Dyn)))
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
    val letrec = typed.asInstanceOf[ELetRec]
    val rhs = letrec.rhs.asInstanceOf[EAscribe]
    val lam = rhs.e.asInstanceOf[ELam]
    val cond = lam.body.asInstanceOf[ECond]

    assertEquals(typed.ty, Some(TInt))
    assertEquals(rhs.ty, Some(TFun(TInt, TInt)))
    assertEquals(cond.st, Some(Sta))
    assertEquals(cond.ty, Some(TInt))
  }

  test("infer handles recursive fix with annotated function body") {
    val src =
      "fix fib. fun(n: Int): Int => if n <= 1 then 1 else n * fib(n - 1)"

    val typed = infer(parse(src))
    val fix = typed.asInstanceOf[EFix]

    assertEquals(typed.ty, Some(TFun(TInt, TInt)))
    assertEquals(fix.st, Some(Sta))
    assertEquals(fix.e.ty, Some(TFun(TInt, TInt)))
  }

  test("infer rejects unannotated recursive letrec") {
    val src =
      "letrec fact = fun(n: Int) => if n <= 1 then 1 else n * fact(n - 1) in fact(5)"

    intercept[TypeException] {
      infer(parse(src))
    }
  }

  test("check treats forall stage binders up to alpha-renaming") {
    val expr =
      parse("fun(x: forall[a]. Int @ a): forall[a]. Int @ a => x")
    val expected =
      TFun(
        TForallSt("b", TAt(TInt, SVar("b"))),
        TForallSt("c", TAt(TInt, SVar("c"))),
      )

    assert(equivType(infer(expr).ty.get, expected))
    val checked = check(expr, expected)
    assertEquals(checked.ty, Some(expected))
  }

  test("stage poly add") {
    val expr = "let add[s] (x: Int@s) (y: Int@s) = x +@s y in add[2](lift[2](2))(lift[2](3))"
    val inferred = infer(parse(expr))
    assert(inferred.ty.get == TInt.at(Dyn))
  }

  test("lift2-lift2") {
    val expr = parse("lift[2](lift[2](1))")
    intercept[TypeException] {
      infer(expr)
    }
  }

  test("second-stage cond should have second-stage branches") {
    intercept[TypeException]:
      Config.elab = false
      val str = """
        if lift[2](true) then 1 else 2
      """
      val checked = check(parse(str), TInt)

    intercept[TypeException]:
      Config.elab = true
      val str = """
        if lift[2](true) then 1 else 2
      """
      val checked = check(parse(str), TInt)
  }

class ElabTest extends FunSuite:
  Config.elab = true

  test("branches") {
    val str = """
      if lift[2](true) then 1 else 2
    """
    val checked = check(parse(str), TInt.at(Dyn))
  }

  test("stage var") {
    val expr = """let add[s] (x: Int@s) (y: Int@s) = x + y in add[2](2)(3)"""
    val inferred = infer(parse(expr))
    assert(inferred.asInstanceOf[ELet].rhs.asInstanceOf[ESLam].body.asInstanceOf[ELam].body.asInstanceOf[ELam].body ==
      EBinOp("+",EVar("x"),EVar("y"),Some(SVar("s"))))
    assert(inferred.ty.get == TInt.at(Dyn))
  }

  test("coerce primitives") {
    {
      val expr = parse("fun(x: Int): Int@2 => 1")
      val inferred = infer(expr)
      assertEquals(inferred, ELam("x",Some(TInt),ELift(ENum(1),SNum(2)),Some(TInt.at(Dyn))))
    }
    {
      val expr = parse("fun(x: Int): Unit@2 => ()")
      val inferred = infer(expr)
      assertEquals(inferred, ELam("x",Some(TInt),ELift(EUnit,SNum(2)),Some(TUnit.at(Dyn))))
    }
    {
      val expr = parse("fun(x: Int): Bool@2 => true")
      val inferred = infer(expr)
      assertEquals(inferred, ELam("x",Some(TInt),ELift(EBool(true),SNum(2)),Some(TBool.at(Dyn))))
    }
  }

  test("coerce var") {
    {
      val expr = parse("fun(x: Int): Int@2 => x")
      val inferred = infer(expr)
      assertEquals(inferred, ELam("x",Some(TInt),ELift(EVar("x"),SNum(2)),Some(TInt.at(Dyn))))
    }
    {
      val expr = parse("sfun[s] => fun(x: Int): Int@s => x")
      val inferred = infer(expr)
      assertEquals(inferred, ESLam("s",ELam("x",Some(TInt),ELift(EVar("x"),SVar("s")),Some(TAt(TInt,SVar("s"))))))
    }
  }


class ElabNegativeTest extends FunSuite:
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

