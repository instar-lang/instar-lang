package instar.parser

import munit.FunSuite

import instar.syntax.*
import instar.syntax.given
import Expr.*
import Stage.*
import Type.*

class ParserTest extends FunSuite:
  test("function annotations preserve independent stages") {
    assertEquals(parseType("(Int@1 -> Int@1)@2"),
      TAt(TFun(TAt(TInt, Sta), TAt(TInt, Sta)), Dyn))
    assertEquals(parseType("(Int@2 -> Int@1)@1"),
      TAt(TFun(TAt(TInt, Dyn), TAt(TInt, Sta)), Sta))
  }

  test("explicit stage 1 is represented by TAt") {
    assertEquals(parseType("Int@1"), TAt(TInt, Sta))
    assertEquals(parseType("Int"), TInt)
  }

  test("Code expands every type annotation to stage 2") {
    assertEquals(parseType("Code[Int -> Int]"),
      TFun(TInt.at(Dyn), TInt.at(Dyn)).at(Dyn))
    assertEquals(parseType("Code[Int@1 -> Int@2]"),
      TFun(TInt.at(Dyn), TInt.at(Dyn)).at(Dyn))
    assertEquals(parseType("Code[Int@s -> Int@a]"),
      TFun(TInt.at(Dyn), TInt.at(Dyn)).at(Dyn))
    assertEquals(parseType("Code[Int]"), TInt.at(Dyn))
    assertEquals(parseType("Code[Bool@1]"), TBool.at(Dyn))
    assertEquals(parseType("Code[Unit@s]"), TUnit.at(Dyn))
    assertEquals(parseType("Code[(Int@1 -> Ref[Int@1])@1 -> Int@1]"),
      TFun(TFun(TInt.at(Dyn), TRef(TInt.at(Dyn)).at(Dyn)).at(Dyn), TInt.at(Dyn)).at(Dyn))
    assertEquals(parseType("Code[forall[s: 1 <= s]. Int@s]"),
      TForallSt("s", TInt.at(Dyn), List(StageConstraint(Sta, SVar("s")))).at(Dyn))
  }

  test("Code and explicit recursive stage annotations have the same parsed type") {
    val code = parseType("Code[Int -> Int]")
    val annotated = parseType("(Int@2 -> Int@2)@2")
    assertEquals(code, TFun(TInt.at(Dyn), TInt.at(Dyn)).at(Dyn))
    assertEquals(annotated, TFun(TInt.at(Dyn), TInt.at(Dyn)).at(Dyn))
    assertEquals(code, annotated)
    assertEquals(parseType("Code[Int -> Int]@1"),
      TAt(TFun(TInt.at(Dyn), TInt.at(Dyn)), Sta))
    assertEquals(parseType("Code[(Int -> Int)@1]"),
      TFun(TInt.at(Dyn), TInt.at(Dyn)).at(Dyn))
  }

  test("nested Code expands idempotently") {
    assertEquals(parseType("Code[Code[Int@1 -> Int@1]]"),
      TFun(TInt.at(Dyn), TInt.at(Dyn)).at(Dyn))
  }

  test("lexes and parses let/fun/application") {
    val input = "let inc = fun(x: Int): Int => x + 1 in inc(41)"
    val parsed = parse(input)

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

  test("parses bare function application left-associatively") {
    val parsed = parse("f x y")
    assertEquals(parsed, EApp(EApp(EVar("f"), EVar("x"), None), EVar("y"), None))
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

    val lam = parsed.asInstanceOf[ESLam]
    assertEquals(lam.s, "s")
    assertEquals(lam.body, ELift(ENum(1), SVar("s")))
    assertEquals(lam.ty, Some(TForallSt("s", TFun(TAt(TInt, SVar("s")), TInt)).at()))
  }

  test("parses constraints on stage abstractions and universal types") {
    val constraints = List(StageConstraint(SVar("a"), SVar("b")), StageConstraint(SVar("b"), Dyn))
    val src = "sfun[a, b: a <= b, b <= 2] => fun(x: Int@a) => lift[b](x)"
    val parsed = parse(src).asInstanceOf[ESLam].body.asInstanceOf[ESLam]
    assertEquals(parsed.s, "b")
    assertEquals(parsed.constraints, constraints)
    val ty = parseType("forall[a, b: a <= b, b <= 2]. Int@a -> Int@b")
    assertEquals(ty, TForallSt("a", TForallSt("b",
      TFun(TAt(TInt, SVar("a")), TAt(TInt, SVar("b"))), constraints)).at())
  }

  test("constrained function headers preserve constraints in their annotations") {
    val header = "let f[a, b: a <= b](x: Int@a): Int@b = lift[b](x) in f[1, 2](3)"
    val expanded = """
      let f: forall[a]. forall[b: a <= b]. Int@a -> Int@b =
        sfun[a] => sfun[b: a <= b] => fun(x: Int@a): Int@b => lift[b](x)
      in f[1, 2](3)
    """
    assertEquals(parse(header), parse(expanded))
  }

  test("rejects malformed constraints and unsupported concrete stages") {
    for src <- List("sfun[s: s < 2] => 1", "sfun[s: s <=] => 1", "lift[0](1)", "lift[3](1)") do
      intercept[ParserException] { parse(src) }
  }

  test("rejects stage join syntax") {
    intercept[Lexer.LexerException] { parse("lift[a | b](1)") }
    intercept[Lexer.LexerException] { parse("lift[a ⊔ b](1)") }
    intercept[Lexer.LexerException] { parse("f[a | b]") }
    intercept[Lexer.LexerException] { parse("f[a ⊔ b]") }
    intercept[Lexer.LexerException] { parseType("Int@(a | b)") }
    intercept[Lexer.LexerException] { parseType("Int@(a ⊔ b)") }
    intercept[Lexer.LexerException] { parse("sfun[a, b, c: a | b <= c] => 1") }
    intercept[Lexer.LexerException] { parse("sfun[a, b, c: a ⊔ b <= c] => 1") }
    intercept[Lexer.LexerException] { parse("x +@(a | b) y") }
    intercept[Lexer.LexerException] { parse("x +@(a ⊔ b) y") }
  }

  test("rejects unparenthesized stage joins after @") {
    intercept[Lexer.LexerException] { parse("lift[2](1) +@1 | 2 lift[2](2)") }
    intercept[Lexer.LexerException] { parse("x +@a | b y") }
    intercept[Lexer.LexerException] { parse("x +@a ⊔ b y") }
    intercept[Lexer.LexerException] { parse("fun@a | b(x: Int) => x") }
    intercept[Lexer.LexerException] { parse("f(x)@a | b") }
    intercept[Lexer.LexerException] { parseType("Int@a | b") }
  }

  test("accepts parenthesized atomic stages after @") {
    assertEquals(parse("lift[2](1) +@(2) lift[2](2)"),
      EBinOp("+", ELift(ENum(1), Dyn), ELift(ENum(2), Dyn), Some(Dyn)))
    assertEquals(parse("f(x)@(a)"), EApp(EVar("f"), EVar("x"), Some(SVar("a"))))
  }

  test("parses let annotation as rhs ascription") {
    val input = "let x: Int = 1 in (x : Int)"
    val parsed = parse(input)

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
        |in add[1] 2 3
        |""".stripMargin

    assertEquals(parse(newSyntax), parse(oldSyntax))
  }

  test("parses refs with explicit stages") {
    val input = "let cell = ref@1(0) in cell :=@s !@1 cell"
    val parsed = parse(input)

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
    val parsed = parse(input)

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
    val parsed = parse(input)

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
    val parsed = parse(input)

    val expected =
      ELetRec(
        "id",
        ESLam("s", ELam("x", Some(TAt(TInt, SVar("s"))), EVar("x"), Some(TAt(TInt, SVar("s"))))),
        EApp(ESApp(EVar("id"), SNum(1)), ENum(3), None),
      )

    assertEquals(parsed, expected)
  }

  test("parses letrec without explicit type even when rhs omits return type") {
    val parsed = parse("letrec id = fun(x: Int) => x in id(3)")

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
      """letrec impPower: forall[s]. Int @ s -> Int -> Ref[Int @ s] @ s -> Int @ s =
        |  sfun[s] => fun(b: Int @ s) => fun(n: Int) => fun(result: Ref[Int @ s] @ s): Int @ s => result
        |in impPower[1](2)(3)(ref(1))
        |""".stripMargin

    val newSyntax =
      """letrec impPower[s] (b: Int @ s) (n: Int) (result: Ref[Int @ s] @ s): Int @ s =
        |  result
        |in impPower[1] 2 3 (ref(1))
        |""".stripMargin

    assertEquals(parse(newSyntax), parse(oldSyntax))
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

  test("parses alternating stage and term binders in letrec bindings") {
    val oldSyntax =
      """letrec mix: Int -> (forall[s]. Int @ s -> Int @ s) =
        |  fun(x: Int) => sfun[s] => fun(y: Int @ s): Int @ s => y
        |in mix(1)[2](lift[2](3))
        |""".stripMargin

    val newSyntax =
      """letrec mix (x: Int) [s] (y: Int @ s): Int @ s =
        |  y
        |in (mix 1)[2] lift[2](3)
        |""".stripMargin

    assertEquals(parse(newSyntax), parse(oldSyntax))
  }

  test("desugars fix without an explicit stage to letrec") {
    val parsed = parse("fix loop. fun(x: Int): Int => x")

    val expected =
      ELetRec("loop", ELam("x", Some(TInt), EVar("x"), Some(TInt)), EVar("loop"))

    assertEquals(parsed, expected)
  }

  test("parses fix with @stage syntax") {
    val parsed = parse("fix@2 loop. fun(x: Int): Int => x")

    val expected =
      ELetRec("loop", ELam("x", Some(TInt), EVar("x"), Some(TInt)), EVar("loop"), Some(Dyn))

    assertEquals(parsed, expected)
  }

  test("parses an explicitly annotated recursive binder") {
    assertEquals(parse("fix loop: Int -> Int. fun(x: Int) => x"),
      ELetRec("loop", EAscribe(ELam("x", Some(TInt), EVar("x"), None), TFun(TInt, TInt)), EVar("loop")))
    assertEquals(parse("fix loop: Int -> Int. fun(x: Int) => x"),
      parse("letrec loop: Int -> Int = fun(x: Int) => x in loop"))
  }

  test("parses a staged recursive binder annotation") {
    assertEquals(parse("fix@2 loop: Code[Int -> Int]. fun@2(x: Code[Int]) => x"),
      ELetRec("loop", EAscribe(ELift(ELam("x", Some(TInt.at(Dyn)), EVar("x"), None), Dyn),
        TFun(TInt.at(Dyn), TInt.at(Dyn)).at(Dyn)), EVar("loop"), Some(Dyn)))
    assertEquals(parse("fix@2 loop: Code[Int -> Int]. fun@2(x: Code[Int]) => x"),
      parse("letrec@2 loop: Code[Int -> Int] = fun@2(x: Code[Int]) => x in loop"))
  }

  test("parses standalone types with constructors, staging, and arrows") {
    val ty = parseType("forall[s]. Ref[Int @ s] @ s -> Code[Int]")
    assertEquals(ty, TForallSt("s", TFun(TAt(TRef(TInt.at(SVar("s"))), SVar("s")), TInt.at(Dyn))).at())
  }

  test("skips line comments in programs") {
    val parsed = parse(
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
    val parsed = parse(
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
    intercept[ParserException] {
      parse("fun(x) => x")
    }
  }
