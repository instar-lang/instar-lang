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
    assertEquals(parse("add{1} 2 3"), parse("add{1}(2)(3)"))
    assertEquals(parse("(mix 1){2} x"), parse("mix(1){2}(x)"))
  }

  test("parses stage abstractions and stage application") {
    val input = "sfun{s}: forall{s}. Int @ s -> Int => lift{s}(1)"
    val parsed = parse(input)

    val lam = parsed.asInstanceOf[ESLam]
    assertEquals(lam.x, "s")
    assertEquals(lam.body, ELift(ENum(1), SVar("s")))
    assertEquals(lam.ty, Some(TForallSt("s", TFun(TAt(TInt, SVar("s")), TInt))))
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
      """let add = sfun{s} => fun(x: Int @ s) => fun(y: Int @ s) => x +@s y
        |in add{1}(2)(3)
        |""".stripMargin

    val newSyntax =
      """let add{s} (x: Int @ s) (y: Int @ s) = x +@s y
        |in add{1} 2 3
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
    val input = "letrec id = sfun{s} => fun(x: Int @ s): Int @ s => x in id{1}(3)"
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
      """letrec impPower: forall{s}. Int @ s -> Int -> Ref[Int] @ s -> Int @ s =
        |  sfun{s} => fun(b: Int @ s) => fun(n: Int) => fun(result: Ref[Int] @ s): Int @ s => result
        |in impPower{1}(2)(3)(ref(1))
        |""".stripMargin

    val newSyntax =
      """letrec impPower{s} (b: Int @ s) (n: Int) (result: Ref[Int] @ s): Int @ s =
        |  result
        |in impPower{1} 2 3 (ref(1))
        |""".stripMargin

    assertEquals(parse(newSyntax), parse(oldSyntax))
  }

  test("desugars comma-separated letrec stage binders to repeated stage abstractions") {
    val oldSyntax =
      """letrec f{s1}{s2} (x: Int @ s2): Int @ s2 =
        |  x
        |in f{1}{1}(2)
        |""".stripMargin

    val newSyntax =
      """letrec f{s1, s2} (x: Int @ s2): Int @ s2 =
        |  x
        |in f{1}{1}(2)
        |""".stripMargin

    assertEquals(parse(newSyntax), parse(oldSyntax))
  }

  test("desugars comma-separated let stage binders to repeated stage abstractions") {
    val oldSyntax =
      """let f{s1}{s2}{s3}{s4} = fun@s1(x: Int @ s2) => x
        |in f{1}{1}{2}{2}(2)
        |""".stripMargin

    val newSyntax =
      """let f{s1, s2, s3, s4} = fun@s1(x: Int @ s2) => x
        |in f{1}{1}{2}{2}(2)
        |""".stripMargin

    assertEquals(parse(newSyntax), parse(oldSyntax))
  }

  test("desugars comma-separated stage application to repeated stage applications") {
    val oldSyntax =
      """let f = sfun{s1} => sfun{s2} => sfun{s3} => fun@s1(x: Int @ s2) => x
        |in f{1}{1}{2}(2)
        |""".stripMargin

    val newSyntax =
      """let f{s1, s2, s3} = fun@s1(x: Int @ s2) => x
        |in f{1, 1, 2}(2)
        |""".stripMargin

    assertEquals(parse(newSyntax), parse(oldSyntax))
  }

  test("parses alternating stage and term binders in letrec bindings") {
    val oldSyntax =
      """letrec mix: Int -> (forall{s}. Int @ s -> Int @ s) =
        |  fun(x: Int) => sfun{s} => fun(y: Int @ s): Int @ s => y
        |in mix(1){2}(lift{2}(3))
        |""".stripMargin

    val newSyntax =
      """letrec mix (x: Int) {s} (y: Int @ s): Int @ s =
        |  y
        |in (mix 1){2} lift{2}(3)
        |""".stripMargin

    assertEquals(parse(newSyntax), parse(oldSyntax))
  }

  test("parses fix without explicit stage as first-stage fix") {
    val parsed = parse("fix loop. fun(x: Int): Int => x")

    val expected =
      EFix(
        "loop",
        ELam("x", Some(TInt), EVar("x"), Some(TInt)),
        None,
      )

    assertEquals(parsed, expected)
  }

  test("parses fix with @stage syntax") {
    val parsed = parse("fix@2 loop. fun(x: Int): Int => x")

    val expected =
      EFix(
        "loop",
        ELam("x", Some(TInt), EVar("x"), Some(TInt)),
        SNum(2),
      )

    assertEquals(parsed, expected)
  }

  test("parses standalone types with constructors, staging, and arrows") {
    val ty = parseType("forall{s}. Ref[Int] @ s -> Code[Int]")
    assertEquals(ty, TForallSt("s", TFun(TAt(TRef(TInt), SVar("s")), TCode(TInt))))
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

  test("parses `tfun[t]` headers and explicit type abstractions") {
    assertEquals(
      parse("let id[t] (x: t) = x in id"),
      ELet(
        "id",
        ETLam("t", ELam("x", Some(TVar("t")), EVar("x"), None)),
        EVar("id"),
      ),
    )
    assertEquals(parse("tfun[t] => 1"), ETLam("t", ENum(1)))
    assertEquals(parse("tfun[t, u] => 1"), ETLam("t", ETLam("u", ENum(1))))
  }

  test("parses type application left-associatively, and applied to terms") {
    assertEquals(parse("f[Int][Bool]"), ETApp(ETApp(EVar("f"), TInt), TBool))
    assertEquals(
      parse("id[Int](5)"),
      EApp(ETApp(EVar("id"), TInt), ENum(5), None),
    )
    assertEquals(
      parse("id[Code[Int]](5)"),
      EApp(ETApp(EVar("id"), TCode(TInt)), ENum(5), None),
    )
  }

  test("parses interleaved type and stage applications") {
    assertEquals(
      parse("h[Int]{2}(x)"),
      EApp(ESApp(ETApp(EVar("h"), TInt), SNum(2)), EVar("x"), None),
    )
    assertEquals(
      parse("h{2}[Int](x)"),
      EApp(ETApp(ESApp(EVar("h"), SNum(2)), TInt), EVar("x"), None),
    )
  }

  test("`[...]` is type application and `{...}` is stage application") {
    assertEquals(parseType("Code[Int]"), TCode(TInt))
    assertEquals(parseType("Ref[Int]"), TRef(TInt))
    assertEquals(parseType("Code[Code[Int]]"), TCode(TCode(TInt)))

    val e = intercept[ParserException] { parse("lift[2](1)") }
    assert(e.getMessage.contains("Expected `{`"), clues(e.getMessage))
  }

  test("`forall[t].` is a type forall, `forall{s}.` a stage forall") {
    assertEquals(
      parseType("forall[t]. t -> t"),
      TForallTy("t", TFun(TVar("t"), TVar("t"))),
    )
    assertEquals(
      parseType("forall{s}. Int -> Int"),
      TForallSt("s", TFun(TInt, TInt)),
    )
    assertEquals(
      parseType("forall[t]. forall[u]. t -> u"),
      TForallTy("t", TForallTy("u", TFun(TVar("t"), TVar("u")))),
    )
  }

  test("`forall{s, u}.` binds several stage variables") {
    assertEquals(
      parseType("forall{s, u}. Int@s"),
      TForallSt("s", TForallSt("u", TAt(TInt, SVar("s")))),
    )
    assertEquals(
      parseType("forall{s}. forall{u}. Int@s"),
      TForallSt("s", TForallSt("u", TAt(TInt, SVar("s")))),
    )
  }

  test("no type scope: an unknown name is a type variable wherever it appears") {
    // No scope is tracked: `t` is a `TVar` here even though nothing binds it.
    assertEquals(
      parse("let id[t] (x: t) = x in (1: t)"),
      ELet(
        "id",
        ETLam("t", ELam("x", Some(TVar("t")), EVar("x"), None)),
        EAscribe(ENum(1), TVar("t")),
      ),
    )
    assertEquals(parse("fun(x: t) => x"), ELam("x", Some(TVar("t")), EVar("x"), None))
    assertEquals(parse("fun(x: T) => x"), ELam("x", Some(TVar("T")), EVar("x"), None))
  }

  test("a type variable cannot take type arguments") {
    val e = intercept[ParserException] {
      parseType("t[Int]")
    }
    assert(e.getMessage.contains("Unsupported type constructor `t`"), clues(e.getMessage))
  }

  test("innermost type binder shadows the outer one") {
    assertEquals(
      parse("tfun[t] => tfun[t] => fun(x: t) => x"),
      ETLam(
        "t",
        ETLam("t", ELam("x", Some(TVar("t")), EVar("x"), None)),
      ),
    )
  }
