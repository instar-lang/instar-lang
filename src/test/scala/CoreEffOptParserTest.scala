package instar.eff.opt

import munit.FunSuite

import Expr.*
import Stage.*
import Type.*

class CoreEffOptParserTest extends FunSuite:

  test("lexes and parses let/fun/application") {
    val input = "let inc = fun(x: Int): Int => x + 1 in inc(41)"
    val parsed = CoreEffOptParser.parse(input)

    val expected =
      ELet(
        "inc",
        ELam(
          "x",
          Some(TInt),
          EBinOp("+", EVar("x"), ENum(1), Sta),
          Some(TInt),
        ),
        EApp(EVar("inc"), ENum(41), Sta),
      )

    assertEquals(parsed, expected)
  }

  test("parses stage abstractions and stage application") {
    val input = "sfun[s]: forall[s]. Int @ s -> Int => lift[s](1)"
    val parsed = CoreEffOptParser.parse(input)

    val lam = parsed.asInstanceOf[ESLam]
    assertEquals(lam.x, "s")
    assertEquals(lam.body, ELift(ENum(1), SVar("s")))
    assertEquals(lam.ty, Some(TForallSt("s", TFun(TAt(TInt, SVar("s")), TInt))))
  }

  test("parses let annotation as rhs ascription") {
    val input = "let x: Int = 1 in (x : Int)"
    val parsed = CoreEffOptParser.parse(input)

    val expected =
      ELet(
        "x",
        EAscribe(ENum(1), TInt),
        EAscribe(EVar("x"), TInt),
      )

    assertEquals(parsed, expected)
  }

  test("parses refs with explicit stages") {
    val input = "let cell = ref@1(0) in assign@s(cell, deref@1(cell))"
    val parsed = CoreEffOptParser.parse(input)

    val expected =
      ELet(
        "cell",
        EAlloc(ENum(0), SNum(1)),
        EAssign(EVar("cell"), EDeref(EVar("cell"), SNum(1)), SVar("s")),
      )

    assertEquals(parsed, expected)
  }

  test("parses letrec with explicit function type") {
    val input = "letrec id: Int -> Int = fun(x: Int): Int => x in id(3)"
    val parsed = CoreEffOptParser.parse(input)

    val expected =
      ELetRec(
        "id",
        TFun(TInt, TInt),
        ELam("x", Some(TInt), EVar("x"), Some(TInt)),
        EApp(EVar("id"), ENum(3), Sta),
      )

    assertEquals(parsed, expected)
  }

  test("rejects unannotated letrec because the target AST requires a type") {
    intercept[CoreEffOptParser.ParserException] {
      CoreEffOptParser.parse("letrec id = fun(x: Int): Int => x in id(3)")
    }
  }

  test("parses standalone types with constructors, staging, and arrows") {
    val ty = CoreEffOptParser.parseType("forall[s]. Ref[Int] @ s -> Code[Int]")
    assertEquals(ty, TForallSt("s", TFun(TAt(TRef(TInt), SVar("s")), TCode(TInt))))
  }
