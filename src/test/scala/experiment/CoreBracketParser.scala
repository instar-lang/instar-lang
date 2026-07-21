package instar.experiment.corebracket

import Stage.*
import Expr.*
import Type.*
import Value.*
import PreExpr.*

class ParseTest extends munit.FunSuite {
  def testParse(source_str: String, target_pexpr: PreExpr): Unit =
    val pexpr = parse(source_str)
    assertEquals(pexpr.toString, target_pexpr.toString())

  test("basics") {
    testParse(
      "1",
      PNum(1)
    )
    testParse(
      "(((true)))",
      PBool(true)
    )
    testParse(
      "(())",
      PUnit
    )

    testParse(
      "if (1==1) then 1 else 1",
      PCond1(PBinOp1("==", PNum(1), PNum(1)), PNum(1), PNum(1))
    )

    testParse(
      "let x = 1 in x",
      PLet("x", PNum(1), PVar("x"))
    )

    testParse(
      "fun (x: Int) => x",
      PLam("x", Some(TInt), PVar("x"), None)
    )

    testParse(
      "let x = fun (x: Int) => x in x 1",
      PLet(
        "x",
        PLam("x", Some(TInt), PVar("x"), None),
        PApp(PVar("x"), PNum(1), Sta)
      )
    )
  }

  test("bracketed") {
    testParse(
      "'1",
      PBracket(PNum(1))
    )
    testParse(
      "'(1+1)",
      PBracket(PBinOp1("+", PNum(1), PNum(1)))
    )

    testParse(
      "$x",
      PEscape(PVar("x"))
    )

    testParse(
      "'-$(x+1)",
      PBracket(
        PUnaryOp("-", PEscape(PBinOp("+", PVar("x"), PNum(1), Sta)), Sta)
      )
    )
    testParse(
      "'-$(x+1)",
      PBracket(
        PUnaryOp("-", PEscape(PBinOp("+", PVar("x"), PNum(1), Sta)), Sta)
      )
    )
  }
}

// adapted tests from test/scala/Parser.scala
class OldParseTest extends munit.FunSuite {
  test("lexes and parses let/fun/application") {
    val input = "let inc = fun(x: Int): Int => x + 1 in inc(41)"
    val parsed = parse(input)

    val expected =
      PLet(
        "inc",
        PLam(
          "x",
          Some(TInt),
          PBinOp("+", PVar("x"), PNum(1), Sta),
          Some(TInt)
        ),
        PApp(PVar("inc"), PNum(41), Sta)
      )

    assertEquals(parsed, expected)
  }

  test("parses bare function application left-associatively") {
    val parsed = parse("f x y")
    assertEquals(parsed, PApp(PApp(PVar("f"), PVar("x"), Sta), PVar("y"), Sta))
  }

  test("parses bare application with parenthesized complex arguments") {
    assertEquals(parse("f x (y + 1)"), parse("f(x)(y + 1)"))
  }

  test("preserves stage application syntax alongside bare term application") {
    assertEquals(parse("add[1] 2 3"), parse("add[1](2)(3)"))
    assertEquals(parse("(mix 1)[2] x"), parse("mix(1)[2](x)"))
  }

  test("parses stage abstractions and stage application") {
    val input = "sfun[s]: forall[s]. Int @ s -> Int => lift[s](1)"
    val parsed = parse(input)

    val lam = parsed.asInstanceOf[PSLam]
    assertEquals(lam.x, "s")
    assertEquals(lam.body, PLift(PNum(1), SVar("s")))
    assertEquals(lam.ty, Some(TForallSt("s", TFun(TAt(TInt, SVar("s")), TInt))))
  }

  test("parses let annotation as rhs ascription") {
    val input = "let x: Int = 1 in (x : Int)"
    val parsed = parse(input)

    val expected =
      PLet(
        "x",
        PAscribe(PNum(1), TInt),
        PAscribe(PVar("x"), TInt)
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
        |in add[1] 2 3
        |""".stripMargin

    assertEquals(parse(newSyntax), parse(oldSyntax))
  }

  test("parses let with explicit function type") {
    val input = "let id: Int -> Int = fun(x: Int): Int => x in id(3)"
    val parsed = parse(input)

    val expected =
      PLet(
        "id",
        PAscribe(
          PLam("x", Some(TInt), PVar("x"), Some(TInt)),
          TFun(TInt, TInt)
        ),
        PApp(PVar("id"), PNum(3), Sta)
      )

    assertEquals(parsed, expected)
  }

  test("parses let without explicit type when rhs exposes one") {
    val input = "let id = fun(x: Int): Int => x in id(3)"
    val parsed = parse(input)

    val expected =
      PLet(
        "id",
        PLam("x", Some(TInt), PVar("x"), Some(TInt)),
        PApp(PVar("id"), PNum(3), Sta)
      )

    assertEquals(parsed, expected)
  }

  test(
    "parses stage-polymorphic let without explicit type when rhs exposes one"
  ) {
    val input = "let id = sfun[s] => fun(x: Int @ s): Int @ s => x in id[1](3)"
    val parsed = parse(input)

    val expected =
      PLet(
        "id",
        PSLam(
          "s",
          PLam(
            "x",
            Some(TAt(TInt, SVar("s"))),
            PVar("x"),
            Some(TAt(TInt, SVar("s")))
          )
        ),
        PApp(PSApp(PVar("id"), SNum(1)), PNum(3), Sta)
      )

    assertEquals(parsed, expected)
  }

  test("parses letrec without explicit type even when rhs omits return type") {
    val parsed = parse("let id = fun(x: Int) => x in id(3)")

    val expected =
      PLet(
        "id",
        PLam("x", Some(TInt), PVar("x"), None),
        PApp(PVar("id"), PNum(3), Sta)
      )

    assertEquals(parsed, expected)
  }

  test("desugars let function bindings to the same AST as sfun/fun") {
    val oldSyntax =
      """let impPower: forall[s]. Int @ s -> Int -> Int @ s -> Int @ s =
        |  sfun[s] => fun(b: Int @ s) => fun(n: Int) => fun(result: Int @ s): Int @ s => result
        |in impPower[1](2)(3)(1)
        |""".stripMargin

    val newSyntax =
      """let impPower[s] (b: Int @ s) (n: Int) (result: Int @ s): Int @ s =
        |  result
        |in impPower[1] 2 3 (1)
        |""".stripMargin

    assertEquals(parse(newSyntax), parse(oldSyntax))
  }

  test("desugars comma-separated let stage binders to repeated brackets") {
    val oldSyntax =
      """let f[s1][s2] (x: Int @ s2): Int @ s2 =
        |  x
        |in f[1][1](2)
        |""".stripMargin

    val newSyntax =
      """let f[s1, s2] (x: Int @ s2): Int @ s2 =
        |  x
        |in f[1][1](2)
        |""".stripMargin

    assertEquals(parse(newSyntax), parse(oldSyntax))
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

    assertEquals(parse(newSyntax), parse(oldSyntax))
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

    assertEquals(parse(newSyntax), parse(oldSyntax))
  }

  // test("parses alternating stage and term binders in letrec bindings") {
  //   val oldSyntax =
  //     """letrec mix: Int -> (forall[s]. Int @ s -> Int @ s) =
  //       |  fun(x: Int) => sfun[s] => fun(y: Int @ s): Int @ s => y
  //       |in mix(1)[2](lift[2](3))
  //       |""".stripMargin

  //   val newSyntax =
  //     """letrec mix (x: Int) [s] (y: Int @ s): Int @ s =
  //       |  y
  //       |in (mix 1)[2] lift[2](3)
  //       |""".stripMargin

  //   assertEquals(parse(newSyntax), parse(oldSyntax))
  // }

  // test("parses fix without explicit stage as first-stage fix") {
  //   val parsed = parse("fix loop. fun(x: Int): Int => x")

  //   val expected =
  //     EFix(
  //       "loop",
  //       PLam("x", Some(TInt), PVar("x"), Some(TInt)),
  //       None,
  //     )

  //   assertEquals(parsed, expected)
  // }

  // test("parses fix with @stage syntax") {
  //   val parsed = parse("fix@2 loop. fun(x: Int): Int => x")

  //   val expected =
  //     EFix(
  //       "loop",
  //       PLam("x", Some(TInt), PVar("x"), Some(TInt)),
  //       SNum(2),
  //     )

  //   assertEquals(parsed, expected)
  // }

  test("parses standalone types with constructors, staging, and arrows") {
    val ty = parseType("forall[s]. Int @ s -> Code[Int]")
    assertEquals(ty, TForallSt("s", TFun(TAt(TInt, SVar("s")), TCode(TInt))))
  }

  test("skips line comments in programs") {
    val parsed = parse("""let x = 1 // keep this ignored
        |in x + 2
        |""".stripMargin)

    val expected =
      PLet(
        "x",
        PNum(1),
        PBinOp("+", PVar("x"), PNum(2), Sta)
      )

    assertEquals(parsed, expected)
  }

  // test("skips block comments in programs") {
  //   val parsed = parse(
  //     """let /* binding */ x = ref(0) in /* read it */ !x
  //       |""".stripMargin)

  //   val expected =
  //     PLet(
  //       "x",
  //       EAlloc(PNum(0), None),
  //       EDeref(PVar("x"), None),
  //     )

  //   assertEquals(parsed, expected)
  // }

  test("rejects fun without a parameter type") {
    intercept[ParserException] {
      parse("fun(x) => x")
    }
  }
}
