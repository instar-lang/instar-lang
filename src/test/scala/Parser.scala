package instar.parser

import munit.FunSuite

import instar.syntax.*
import Expr.*
import Stage.*
import Type.*

class ParserTest extends FunSuite:

  test("lexes and parses let/fun/application") {
    val input = "let inc = fun(x: Int): Int => x + 1 in inc(41)"
    val parsed = Parser.parse(input)

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
    val parsed = Parser.parse(input)

    val lam = parsed.asInstanceOf[ESLam]
    assertEquals(lam.x, "s")
    assertEquals(lam.body, ELift(ENum(1), SVar("s")))
    assertEquals(lam.ty, Some(TForallSt("s", TFun(TAt(TInt, SVar("s")), TInt))))
  }

  test("parses let annotation as rhs ascription") {
    val input = "let x: Int = 1 in (x : Int)"
    val parsed = Parser.parse(input)

    val expected =
      ELet(
        "x",
        EAscribe(ENum(1), TInt),
        EAscribe(EVar("x"), TInt),
      )

    assertEquals(parsed, expected)
  }

  test("parses refs with explicit stages") {
    val input = "let cell = ref@1(0) in cell :=@s !@1 cell"
    val parsed = Parser.parse(input)

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
    val parsed = Parser.parse(input)

    val expected =
      ELetRec(
        "id",
        EAscribe(
          ELam("x", Some(TInt), EVar("x"), Some(TInt)),
          TFun(TInt, TInt)),
        EApp(EVar("id"), ENum(3), Sta),
      )

    assertEquals(parsed, expected)
  }

  test("parses letrec without explicit type when rhs exposes one") {
    val input = "letrec id = fun(x: Int): Int => x in id(3)"
    val parsed = Parser.parse(input)

    val expected =
      ELetRec(
        "id",
        ELam("x", Some(TInt), EVar("x"), Some(TInt)),
        EApp(EVar("id"), ENum(3), Sta),
      )

    assertEquals(parsed, expected)
  }

  test("parses stage-polymorphic letrec without explicit type when rhs exposes one") {
    val input = "letrec id = sfun[s] => fun(x: Int @ s): Int @ s => x in id[1](3)"
    val parsed = Parser.parse(input)

    val expected =
      ELetRec(
        "id",
        ESLam("s", ELam("x", Some(TAt(TInt, SVar("s"))), EVar("x"), Some(TAt(TInt, SVar("s"))))),
        EApp(ESApp(EVar("id"), SNum(1)), ENum(3), Sta),
      )

    assertEquals(parsed, expected)
  }

  test("parses letrec without explicit type even when rhs omits return type") {
    val parsed = Parser.parse("letrec id = fun(x: Int) => x in id(3)")

    val expected =
      ELetRec(
        "id",
        ELam("x", Some(TInt), EVar("x"), None),
        EApp(EVar("id"), ENum(3), Sta),
      )

    assertEquals(parsed, expected)
  }

  test("parses fix without explicit stage as first-stage fix") {
    val parsed = Parser.parse("fix loop. fun(x: Int): Int => x")

    val expected =
      EFix(
        "loop",
        ELam("x", Some(TInt), EVar("x"), Some(TInt)),
        Sta,
      )

    assertEquals(parsed, expected)
  }

  test("parses fix with @stage syntax") {
    val parsed = Parser.parse("fix@2 loop. fun(x: Int): Int => x")

    val expected =
      EFix(
        "loop",
        ELam("x", Some(TInt), EVar("x"), Some(TInt)),
        SNum(2),
      )

    assertEquals(parsed, expected)
  }

  test("parses standalone types with constructors, staging, and arrows") {
    val ty = Parser.parseType("forall[s]. Ref[Int] @ s -> Code[Int]")
    assertEquals(ty, TForallSt("s", TFun(TAt(TRef(TInt), SVar("s")), TCode(TInt))))
  }

  test("rejects fun without a parameter type") {
    intercept[Parser.ParserException] {
      Parser.parse("fun(x) => x")
    }
  }
