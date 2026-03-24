package instar.typing

import munit.FunSuite

import instar.parser.Parser
import instar.syntax.*
import instar.syntax.given
import Expr.*
import Stage.*
import Type.*

class Fixme extends FunSuite:
  test("stage poly inst1") {
    val str = """
      let f[s1, s2] = fun@s1(x: Int @ s2) => x in
      f
    """
    val checked = infer(Parser.parse(str))
    println(checked.ty)
    // Got: TCode(TFun(TCode(TInt),TCode(TInt)))
    // Should be: TCode(TFun(TInt, TInt))
  }

class TypingTest extends FunSuite:

  test("stage-poly function") {
    val str1 = """
      let f[s] = fun@s(x: Int @ s) => x in
      let g[s] = f[s] in
      g[2]
    """
    val checked1 = infer(Parser.parse(str1))
    assert(checked1.ty == Some(TCode(TFun(TInt, TInt))))

    val str2 = """
      let f[s] = fun@s(x: Int @ s) => x in
      let g[s] = f[s] in
      g[1]
    """
    val checked2 = infer(Parser.parse(str2))
    assert(checked2.ty == Some(TFun(TInt, TInt)))
  }

  test("multiple stage vars") {
    val str = """
      let f[s1] [s2] = fun@s1(x: Int @ s2) => x in
      f[1][1]
    """
    val checked = infer(Parser.parse(str))
    assert(checked.ty == Some(TFun(TInt, TInt)))
  }

  test("infer resolves omitted first-stage markers") {
    val typed = infer(Parser.parse("let inc = fun(x: Int): Int => x + 1 in inc(41)"))

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
    val checked = check(Parser.parse("fun(x: Int) => x"), TFun(TInt, TInt))

    val lam = checked.asInstanceOf[ELam]
    assertEquals(checked.ty, Some(TFun(TInt, TInt)))
    assertEquals(lam.argTy, Some(TInt))
    assertEquals(lam.retTy, Some(TInt))
    assertEquals(lam.body.ty, Some(TInt))
  }

  test("infer instantiates stage-polymorphic expressions") {
    val typed = infer(Parser.parse("(sfun[s] => lift[s](fun(x: Int @ s): Int @ s => x))[2]"))
    assertEquals(typed.ty, Some(TCode(TFun(TInt, TInt))))
    val inst = typed.asInstanceOf[ESApp]
    assertEquals(inst.st, SNum(2))
  }

  test("infer handles annotated letrec from parser output") {
    val src = """
      letrec fact: Int -> Int =
        fun(n: Int): Int => if n <= 1 then 1 else n * fact(n - 1)
      in fact(5)
    """
    val typed = infer(Parser.parse(src))
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

    val typed = infer(Parser.parse(src))
    val fix = typed.asInstanceOf[EFix]

    assertEquals(typed.ty, Some(TFun(TInt, TInt)))
    assertEquals(fix.st, Some(Sta))
    assertEquals(fix.e.ty, Some(TFun(TInt, TInt)))
  }

  test("infer rejects unannotated recursive letrec") {
    val src =
      "letrec fact = fun(n: Int) => if n <= 1 then 1 else n * fact(n - 1) in fact(5)"

    intercept[TypeException] {
      infer(Parser.parse(src))
    }
  }

  test("check treats forall stage binders up to alpha-renaming") {
    val expr =
      Parser.parse("fun(x: forall[a]. Int @ a): forall[a]. Int @ a => x")
    val expected =
      TFun(
        TForallSt("b", TAt(TInt, SVar("b"))),
        TForallSt("c", TAt(TInt, SVar("c"))),
      )

    assert(equivType(infer(expr).ty.get, expected))
    val checked = check(expr, expected)
    assertEquals(checked.ty, Some(expected))
  }
