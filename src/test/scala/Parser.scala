package instar.parser

import munit.FunSuite

import instar.syntax.*
import instar.syntax.given
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
          EBinOp("+", EVar("x"), ENum(1), None),
          Some(TInt),
        ),
        EApp(EVar("inc"), ENum(41), None),
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

  test("desugars let function bindings to the same AST as sfun/fun") {
    val oldSyntax =
      """let add = sfun[s] => fun(x: Int @ s) => fun(y: Int @ s) => x +@s y
        |in add[1](2)(3)
        |""".stripMargin

    val newSyntax =
      """let add[s] (x: Int @ s) (y: Int @ s) = x +@s y
        |in add[1](2)(3)
        |""".stripMargin

    assertEquals(Parser.parse(newSyntax), Parser.parse(oldSyntax))
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
        EApp(EVar("id"), ENum(3), None),
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
        EApp(EVar("id"), ENum(3), None),
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
        EApp(ESApp(EVar("id"), SNum(1)), ENum(3), None),
      )

    assertEquals(parsed, expected)
  }

  test("parses letrec without explicit type even when rhs omits return type") {
    val parsed = Parser.parse("letrec id = fun(x: Int) => x in id(3)")

    val expected =
      ELetRec(
        "id",
        ELam("x", Some(TInt), EVar("x"), None),
        EApp(EVar("id"), ENum(3), None),
      )

    assertEquals(parsed, expected)
  }

  test("desugars letrec function bindings to the same AST as sfun/fun") {
    val oldSyntax =
      """letrec impPower: forall[s]. Int @ s -> Int -> Ref[Int] @ s -> Int @ s =
        |  sfun[s] => fun(b: Int @ s) => fun(n: Int) => fun(result: Ref[Int] @ s): Int @ s => result
        |in impPower[1](2)(3)(ref(1))
        |""".stripMargin

    val newSyntax =
      """letrec impPower[s] (b: Int @ s) (n: Int) (result: Ref[Int] @ s): Int @ s =
        |  result
        |in impPower[1](2)(3)(ref(1))
        |""".stripMargin

    assertEquals(Parser.parse(newSyntax), Parser.parse(oldSyntax))
  }

  test("desugars comma-separated letrec stage binders to repeated brackets") {
    val oldSyntax =
      """letrec f[s1][s2] (x: Int @ s2): Int @ s2 =
        |  x
        |in f[1][1](2)
        |""".stripMargin

    val newSyntax =
      """letrec f[s1, s2] (x: Int @ s2): Int @ s2 =
        |  x
        |in f[1][1](2)
        |""".stripMargin

    assertEquals(Parser.parse(newSyntax), Parser.parse(oldSyntax))
  }

  test("desugars comma-separated let stage binders to repeated brackets") {
    val oldSyntax =
      """let f[s1][s2][s3][s4] = fun@s1(x: Int @ s2) => x
        |in f[1][1][2][2](2)
        |""".stripMargin

    val newSyntax =
      """let f[s1, s2, s3, s4] = fun@s1(x: Int @ s2) => x
        |in f[1][1][2][2](2)
        |""".stripMargin

    assertEquals(Parser.parse(newSyntax), Parser.parse(oldSyntax))
  }

  test("desugars comma-separated stage application to repeated brackets") {
    val oldSyntax =
      """let f = sfun[s1] => sfun[s2] => sfun[s3] => fun@s1(x: Int @ s2) => x
        |in f[1][1][2](2)
        |""".stripMargin

    val newSyntax =
      """let f[s1, s2, s3] = fun@s1(x: Int @ s2) => x
        |in f[1, 1, 2](2)
        |""".stripMargin

    assertEquals(Parser.parse(newSyntax), Parser.parse(oldSyntax))
  }

  test("parses alternating stage and term binders in letrec bindings") {
    val oldSyntax =
      """letrec mix: Int -> (forall[s]. Int @ s -> Int @ s) =
        |  fun(x: Int) => sfun[s] => fun(y: Int @ s): Int @ s => y
        |in mix(1)[2](lift[2](3))
        |""".stripMargin

    val newSyntax =
      """letrec mix (x: Int) [s] (y: Int @ s): Int @ s =
        |  y
        |in mix(1)[2](lift[2](3))
        |""".stripMargin

    assertEquals(Parser.parse(newSyntax), Parser.parse(oldSyntax))
  }

  test("parses fix without explicit stage as first-stage fix") {
    val parsed = Parser.parse("fix loop. fun(x: Int): Int => x")

    val expected =
      EFix(
        "loop",
        ELam("x", Some(TInt), EVar("x"), Some(TInt)),
        None,
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

  test("skips line comments in programs") {
    val parsed = Parser.parse(
      """let x = 1 // keep this ignored
        |in x + 2
        |""".stripMargin)

    val expected =
      ELet(
        "x",
        ENum(1),
        EBinOp("+", EVar("x"), ENum(2), None),
      )

    assertEquals(parsed, expected)
  }

  test("skips block comments in programs") {
    val parsed = Parser.parse(
      """let /* binding */ x = ref(0) in /* read it */ !x
        |""".stripMargin)

    val expected =
      ELet(
        "x",
        EAlloc(ENum(0), None),
        EDeref(EVar("x"), None),
      )

    assertEquals(parsed, expected)
  }

  test("rejects fun without a parameter type") {
    intercept[Parser.ParserException] {
      Parser.parse("fun(x) => x")
    }
  }
