package instar.interp

import instar.parser.Parser
import instar.syntax.*
import instar.syntax.given
import Expr.*
import Stage.*
import Value.*

trait SurfaceBase extends munit.FunSuite {
  // normalizeExpr/normalizeValue removes type annotations and ascriptions
  private def normalizeExpr(e: Expr): Expr =
    e match
      case EUnit => EUnit
      case ENum(i) => ENum(i)
      case EBool(b) => EBool(b)
      case EVar(name) => EVar(name)
      case ESLam(x, body) => ESLam(x, normalizeExpr(body))
      case ESApp(expr, st) => ESApp(normalizeExpr(expr), st)
      case ELam(x, _, body, _) => ELam(x, None, normalizeExpr(body), None)
      case EBNLam(x, _, body, _) => EBNLam(x, None, normalizeExpr(body), None)
      case EApp(e1, e2, st) => EApp(normalizeExpr(e1), normalizeExpr(e2), st)
      case ELift(t, to) => ELift(normalizeExpr(t), to)
      case ERun(t) => ERun(normalizeExpr(t))
      case ELet(x, rhs, body) => ELet(x, normalizeExpr(rhs), normalizeExpr(body))
      case ELetRec(f, rhs, body) => ELetRec(f, normalizeExpr(rhs), normalizeExpr(body))
      case ECond(e1, e2, e3, st) => ECond(normalizeExpr(e1), normalizeExpr(e2), normalizeExpr(e3), st)
      case EBinOp(op, e1, e2, st) => EBinOp(op, normalizeExpr(e1), normalizeExpr(e2), st)
      case EUnaryOp(op, e1, st) => EUnaryOp(op, normalizeExpr(e1), st)
      case EAlloc(e1, st) => EAlloc(normalizeExpr(e1), st)
      case EDeref(e1, st) => EDeref(normalizeExpr(e1), st)
      case EAssign(e1, e2, st) => EAssign(normalizeExpr(e1), normalizeExpr(e2), st)
      case EAscribe(e1, _) => normalizeExpr(e1)
      case EFix(f, e1, st) => EFix(f, normalizeExpr(e1), st)
      case ELoc(l) => ELoc(l)
      case EIsApp(e1) => EIsApp(normalizeExpr(e1))
      case ECBNApp(e1, e2) => ECBNApp(normalizeExpr(e1), normalizeExpr(e2))

  private def normalizeValue(v: Value): String =
    v match
      case VUnit => "VUnit"
      case VNum(i) => s"VNum($i)"
      case VBool(b) => s"VBool($b)"
      case VLoc(loc) => s"VLoc($loc)"
      case VSClo(st, body, ρ, ς) => s"VSClo($st,${normalizeExpr(body)},$ρ,$ς)"
      case VClo(x, _, body, _, ρ, ς) => s"VClo($x,${normalizeExpr(body)},$ρ,$ς)"
      case VBNClo(x, _, body, _, ρ, ς) => s"VBNClo($x,${normalizeExpr(body)},$ρ,$ς)"
      case VCode(t) => s"VCode(${normalizeExpr(t)})"
      case VThunk(e, ρ, ς) => s"VThunk(${normalizeExpr(e)},$ρ,$ς)"

  protected def testEvalSurface(src: String, expected: Value, opt: Set[String] = Set()): Unit =
    Opt.disableAll
    Opt.enable(opt.toSeq*)
    val (value, _) = eval(Parser.parse(src))
    assertEquals(normalizeValue(value), normalizeValue(expected))
}

class Inspection extends SurfaceBase {
  test("is-app-1") {
    val src = """
    let app = lift[2](fun(x: Int @ 2) => x)(lift[2](42))@2 in
    if isApp(app) then lift[2](true) else lift[2](false)
    """
    testEvalSurface(src,
      VCode(
        ELet("x1", ELam("x0", None, EVar("x0"), None),
          ELet("x2", EApp(EVar("x1"), ENum(42), Sta), EBool(true)))))
  }

  test("is-app-2") {
    testEvalSurface("isApp(lift[2](42))", VBool(false))
  }

  test("is-app-conflict") {
    val src = "lift[2](isApp(lift[2](fun(x: Int @ 2) => x)(lift[2](42))@2))"
    testEvalSurface(src,
      VCode(
        ELet("x1", ELam("x0", None, EVar("x0"), None),
          ELet("x2", EApp(EVar("x1"), ENum(42), Sta), EBool(true)))),
      Set("dce"))
    testEvalSurface(src, VCode(EBool(false)), Set("fun-inline", "dce"))
  }
}

class Core extends SurfaceBase {
  private val lamAddSrc = "lift[2](fun(x: Int @ 2) => x +@2 lift[2](1))"
  private val lamMulSrc = "lift[2](fun(y: Int @ 2) => y *@2 lift[2](42))"
  private val lamAddBody = ELet("x1", EBinOp("+", EVar("x0"), ENum(1), Sta), EVar("x1"))
  private val lamAddCode = ELet("x2", ELam("x0", None, lamAddBody, None), EVar("x2"))
  private val lamMulBody = ELet("x5", EBinOp("*", EVar("x4"), ENum(42), Sta), EVar("x5"))
  private val lamMulCode = ELet("x6", ELam("x4", None, lamMulBody, None), EVar("x6"))

  test("lam-app") {
    testEvalSurface(s"$lamAddSrc(lift[2](41))@2",
      VCode(ELet("x2", ELam("x0", None, lamAddBody, None),
        ELet("x3", EApp(EVar("x2"), ENum(41), Sta), EVar("x3")))))
    testEvalSurface(lamAddSrc,
      VCode(lamAddCode))
  }

  test("fun-stage-sugar") {
    val src = "fun@2(x: Int @ 2) => x +@2 lift[2](1)"
    testEvalSurface(src, VCode(lamAddCode))
  }

  test("cond") {
    val src = s"if@2 lift[2](true) then $lamAddSrc(lift[2](10))@2 else $lamMulSrc(lift[2](20))@2"
    testEvalSurface(src,
      VCode(
        ELet("x8",
          ECond(
            EBool(true),
            ELet("x2", ELam("x0", None, lamAddBody, None),
              ELet("x3", EApp(EVar("x2"), ENum(10), Sta), EVar("x3"))),
            ELet("x6", ELam("x4", None, lamMulBody, None),
              ELet("x7", EApp(EVar("x6"), ENum(20), Sta), EVar("x7"))),
            Sta),
          EVar("x8"))))
  }

  test("stage-poly") {
    testEvalSurface("(sfun[s] => lift[s](fun(x: Int @ s) => x +@s lift[s](1))(lift[s](5))@s)[1]", VNum(6))
    testEvalSurface("(sfun[s] => lift[s](fun(x: Int @ s) => x +@s lift[s](1))(lift[s](5))@s)[2]",
      VCode(ELet("x2", ELam("x0", None, lamAddBody, None),
        ELet("x3", EApp(EVar("x2"), ENum(5), Sta), EVar("x3")))))
  }

  test("let-header-sugar") {
    val src = "let add[s] (x: Int @ s) (y: Int @ s) = x +@s y in add[1](2)(3)"
    testEvalSurface(src, VNum(5))
  }

  test("rec") {
    val factSrc =
      "letrec fact: Int -> Int = fun(n: Int): Int => if n <= 1 then 1 else n * fact(n - 1) in fact(5)"
    val powerSrc =
      "letrec power: Int -> Int -> Int = fun(x: Int) => fun(n: Int): Int => if n == 0 then 1 else x * power(x)(n - 1) in power(2)(10)"
    testEvalSurface(factSrc, VNum(120))
    testEvalSurface(powerSrc, VNum(1024))
  }

  test("rec-stage-poly") {
    val runtimeSrc = """
      letrec power: forall[s]. Int @ s -> Int -> Int @ s =
        sfun[s] => fun(x: Int @ s) => fun(n: Int): Int @ s =>
          if n == 0 then lift[s](1) else x *@s power[s](x)(n - 1)
      in power[1](2)(3)
    """

    val codeSrc = """
      letrec power: forall[s]. Int @ s -> Int -> Int @ s =
        sfun[s] => fun(x: Int @ s) => fun(n: Int): Int @ s =>
          if n == 0 then lift[s](1) else x *@s power[s](x)(n - 1)
      in lift[2](fun(x: Code[Int]): Code[Int] => power[2](x)(3))
    """

    testEvalSurface(runtimeSrc, VNum(8))
    testEvalSurface(codeSrc,
      VCode(
        ELet("x4",
          ELam("x0", None,
            ELet("x1", EBinOp("*", EVar("x0"), ENum(1), Sta),
              ELet("x2", EBinOp("*", EVar("x0"), EVar("x1"), Sta),
                ELet("x3", EBinOp("*", EVar("x0"), EVar("x2"), Sta), EVar("x3")))),
            None),
          EVar("x4"))))
  }

  test("rec-imp-stage-poly") {
    val runtimeSrc = """
      letrec impPower: forall[s]. Int @ s -> Int -> Ref[Int]@s -> Int @ s =
        sfun[s] => fun(b: Int @ s) => fun(n: Int) => fun(result: Ref[Int]@s): Int @ s =>
          if n == 0 then !@s result else let _ = result :=@s b *@s !@s result in impPower[s](b)(n - 1)(result)
      in impPower[1](2)(3)(ref(1))
    """
    val codeSrc = """
      letrec impPower: forall[s]. Int @ s -> Int -> Ref[Int]@s -> Int @ s =
        sfun[s] => fun(b: Int @ s) => fun(n: Int) => fun(result: Ref[Int]@s): Int @ s =>
          if n == 0 then !@s result else let _ = result :=@s b *@s !@s result in impPower[s](b)(n - 1)(result)
      in lift[2](fun(x: Code[Int]): Code[Int] => impPower[2](x)(3)(ref@2(lift[2](1))))
    """

    testEvalSurface(runtimeSrc, VNum(8))
    testEvalSurface(codeSrc,
      VCode(
        ELet("x12",
          ELam("x0", None,
            ELet("x1", EAlloc(ENum(1), Sta),
              ELet("x2", EDeref(EVar("x1"), Sta),
                ELet("x3", EBinOp("*", EVar("x0"), EVar("x2"), Sta),
                  ELet("x4", EAssign(EVar("x1"), EVar("x3"), Sta),
                    ELet("x5", EDeref(EVar("x1"), Sta),
                      ELet("x6", EBinOp("*", EVar("x0"), EVar("x5"), Sta),
                        ELet("x7", EAssign(EVar("x1"), EVar("x6"), Sta),
                          ELet("x8", EDeref(EVar("x1"), Sta),
                            ELet("x9", EBinOp("*", EVar("x0"), EVar("x8"), Sta),
                              ELet("x10", EAssign(EVar("x1"), EVar("x9"), Sta),
                                ELet("x11", EDeref(EVar("x1"), Sta), EVar("x11")))))))))))),
            None),
          EVar("x12"))))
  }

  test("rec-imp-stage-poly letrec-header-sugar") {
    val runtimeSrc = """
      letrec impPower[s] (b: Int @ s) (n: Int) (result: Ref[Int]@s): Int @ s =
        if n == 0 then !@s result else let _ = result :=@s b *@s !@s result in impPower[s](b)(n - 1)(result)
      in impPower[1](2)(3)(ref(1))
    """

    testEvalSurface(runtimeSrc, VNum(8))
  }

  test("stuck") {
    intercept[RuntimeException] {
      eval(Parser.parse("let x = ref@2(lift[2](0)) in 10"))
    }
  }

  test("fix-fib") {
    val src = "let fib = fix fib. fun(n: Int): Int => if n <= 1 then 1 else n * fib(n - 1) in fib(5)"
    testEvalSurface(src, VNum(120))
  }

  test("fix-default-stage") {
    val src = "let fib = fix fib. fun(n: Int): Int => if n <= 1 then 1 else n * fib(n - 1) in fib(5)"
    testEvalSurface(src, VNum(120))
  }

  test("letrec-fib") {
    val src = "letrec fib: Int -> Int = fun(n: Int) => if n <= 1 then 1 else n * fib(n - 1) in fib(5)"
    testEvalSurface(src, VNum(120))
  }

  test("fix-second-stage") {
    val src = """
      let fib = fix@2 fib. lift[2](fun(n: Code[Int]): Code[Int] =>
        if@2 n <=@2 lift[2](1) then lift[2](1) else n *@2 fib(n -@2 lift[2](1))@2)
      in fib(lift[2](5))@2
    """

    testEvalSurface(src,
      VCode(
        ELet("x8",
          EFix("f0",
            ELet("x7",
              ELam("x1", None,
                ELet("x2", EBinOp("<=", EVar("x1"), ENum(1), Sta),
                  ELet("x6",
                    ECond(EVar("x2"), ENum(1),
                      ELet("x3", EBinOp("-", EVar("x1"), ENum(1), Sta),
                        ELet("x4", EApp(EVar("f0"), EVar("x3"), Sta),
                          ELet("x5", EBinOp("*", EVar("x1"), EVar("x4"), Sta), EVar("x5")))),
                      Sta),
                    EVar("x6"))),
                None),
              EVar("x7")),
            Sta),
          ELet("x9", EApp(EVar("x8"), ENum(5), Sta), EVar("x9")))))
  }

  test("lift-loc") {
    testEvalSurface("lift[2](ref@1(42))", VCode(ELet("x0", ELoc(0), EVar("x0"))))
  }

  test("lift-curry-lam") {
    val src = "lift[2](fun(x: Int @ 2) => lift[2](fun(y: Int @ 2) => x +@2 y))"
    testEvalSurface(src,
      VCode(
        ELet("x4",
          ELam("x0", None,
            ELet("x3",
              ELam("x1", None,
                ELet("x2", EBinOp("+", EVar("x0"), EVar("x1"), Sta), EVar("x2")),
                None),
              EVar("x3")),
            None),
          EVar("x4"))))
  }

  test("run") {
    testEvalSurface("1", VNum(1))
    testEvalSurface("run(lift[2](1))", VNum(1))
    testEvalSurface(lamAddSrc, VCode(lamAddCode))
    testEvalSurface(s"run($lamAddSrc)", VClo("x0", None, lamAddBody, None, Map(), Map()))

    val appSrc = s"let y = $lamAddSrc in y(lift[2](1))@2"
    testEvalSurface(appSrc,
      VCode(ELet("x2", ELam("x0", None, lamAddBody, None),
        ELet("x3", EApp(EVar("x2"), ENum(1), Sta), EVar("x3")))))

    testEvalSurface("!(run(lift[2](ref@1(1))))", VNum(1))
  }
}

class CoreOpt extends SurfaceBase {
  private def vcode(e: Expr): Value = VCode(e)

  private val add2LamSrc = "lift[2](fun(y: Int @ 2) => y +@2 lift[2](2))"

  test("opt-rewriting-1") {
    val src = "let x = lift[2](1) +@2 lift[2](2) in let y = lift[2](1) +@2 lift[2](2) in x *@2 y"
    testEvalSurface(src, vcode(ENum(9)), Set("rewriting"))
  }

  test("opt-rewriting-2") {
    val src = "lift[2](fun(z: Int @ 2) => let x = z +@2 lift[2](2) in let y = lift[2](1) +@2 lift[2](2) in x *@2 y)"
    testEvalSurface(src,
      vcode(
        ELet("x3",
          ELam("x0", None,
            ELet("x1", EBinOp("+", EVar("x0"), ENum(2), Sta),
              ELet("x2", EBinOp("*", EVar("x1"), ENum(3), Sta), EVar("x2"))),
            None),
          EVar("x3"))),
      Set("rewriting"))
  }

  test("opt-dce") {
    val src = "lift[2](fun(y: Int @ 2) => let z = y +@2 lift[2](2) in y)"
    testEvalSurface(src,
      vcode(ELet("x2", ELam("x0", None, EVar("x0"), None), EVar("x2"))),
      Set("dce"))
  }

  test("opt-no-let-lam") {
    val src = s"$add2LamSrc(lift[2](3))@2"
    testEvalSurface(src,
      vcode(
        ELet("x2",
          EApp(ELam("x0", None, ELet("x1", EBinOp("+", EVar("x0"), ENum(2), Sta), EVar("x1")), None), ENum(3), Sta),
          EVar("x2"))),
      Set("no-let-lam"))
  }

  test("opt-app-inline-1") {
    val src = s"$add2LamSrc(lift[2](3))@2"
    testEvalSurface(src,
      vcode(ELet("x2", EBinOp("+", ENum(3), ENum(2), Sta), EVar("x2"))),
      Set("fun-inline", "no-let-lam"))
  }

  test("opt-app-inline-2") {
    val src = s"$add2LamSrc(lift[2](3))@2"
    testEvalSurface(src,
      vcode(ELet("x3", EBinOp("+", ENum(3), ENum(2), Sta), EVar("x3"))),
      Set("fun-inline", "dce"))
  }

  test("opt-app-inline-3") {
    val src = "lift[2](fun(z: Code[Int -> Int]) => z(lift[2](3))@2)"
    testEvalSurface(src,
      vcode(
        ELet("x2",
          ELam("x0", None,
            ELet("x1", EApp(EVar("x0"), ENum(3), Sta), EVar("x1")),
            None),
          EVar("x2"))),
      Set("fun-inline"))
  }

  test("opt-app-inline-4") {
    val src = """
      let a = lift[2](42) +@2 lift[2](42) in
      lift[2](fun(z: Int @ 2) =>
        let f = lift[2](fun(z: Int @ 2) =>
          let x = z +@2 a in
          let y = lift[2](1) +@2 lift[2](2) in
          x *@2 y)
        in f(z)@2)
    """
    testEvalSurface(src,
      vcode(
        ELet("x0", EBinOp("+", ENum(42), ENum(42), Sta),
          ELet("x10",
            ELam("x1", None,
              ELet("x6",
                ELam("x2", None,
                  ELet("x3", EBinOp("+", EVar("x2"), EVar("x0"), Sta),
                    ELet("x4", EBinOp("+", ENum(1), ENum(2), Sta),
                      ELet("x5", EBinOp("*", EVar("x3"), EVar("x4"), Sta), EVar("x5")))),
                  None),
                ELet("x7", EBinOp("+", EVar("x1"), EVar("x0"), Sta),
                  ELet("x8", EBinOp("+", ENum(1), ENum(2), Sta),
                    ELet("x9", EBinOp("*", EVar("x7"), EVar("x8"), Sta), EVar("x9"))))),
              None),
            EVar("x10")))),
      Set("fun-inline"))
  }

  test("opt-app-inline-nested-1") {
    val src = """
      let f1 = lift[2](fun(y: Int @ 2) => y +@2 lift[2](2)) in
      let f2 = lift[2](fun(z: Int @ 2) => f1(z)@2) in
      f2(lift[2](3))@2
    """
    testEvalSurface(src,
      vcode(ELet("x6", EBinOp("+", ENum(3), ENum(2), Sta), EVar("x6"))),
      Set("fun-inline", "dce"))
  }

  test("opt-app-inline-cse") {
    val src = """
      let f1 = lift[2](fun(y: Int @ 2) =>
        (lift[2](42) *@2 lift[2](100)) +@2 (y +@2 lift[2](2))) in
      let r = f1(lift[2](3))@2 in
      let a = lift[2](42) *@2 lift[2](100) in
      r /@2 a
    """

    testEvalSurface(src,
      vcode(
        ELet("x4",
          ELam("x0", None,
            ELet("x1", EBinOp("*", ENum(42), ENum(100), Sta),
              ELet("x2", EBinOp("+", EVar("x0"), ENum(2), Sta),
                ELet("x3", EBinOp("+", EVar("x1"), EVar("x2"), Sta), EVar("x3")))),
            None),
          ELet("x5", EApp(EVar("x4"), ENum(3), Sta),
            ELet("x6", EBinOp("*", ENum(42), ENum(100), Sta),
              ELet("x7", EBinOp("/", EVar("x5"), EVar("x6"), Sta), EVar("x7")))))),
      Set())

    testEvalSurface(src,
      vcode(
        ELet("x4",
          ELam("x0", None,
            ELet("x1", EBinOp("*", ENum(42), ENum(100), Sta),
              ELet("x2", EBinOp("+", EVar("x0"), ENum(2), Sta),
                ELet("x3", EBinOp("+", EVar("x1"), EVar("x2"), Sta), EVar("x3")))),
            None),
          ELet("x5", EBinOp("*", ENum(42), ENum(100), Sta),
            ELet("x6", EBinOp("+", ENum(3), ENum(2), Sta),
              ELet("x7", EBinOp("+", EVar("x5"), EVar("x6"), Sta),
                ELet("x8", EBinOp("*", ENum(42), ENum(100), Sta),
                  ELet("x9", EBinOp("/", EVar("x7"), EVar("x8"), Sta), EVar("x9")))))))),
      Set("fun-inline"))

    testEvalSurface(src,
      vcode(
        ELet("x4",
          ELam("x0", None,
            ELet("x1", EBinOp("*", ENum(42), ENum(100), Sta),
              ELet("x2", EBinOp("+", EVar("x0"), ENum(2), Sta),
                ELet("x3", EBinOp("+", EVar("x1"), EVar("x2"), Sta), EVar("x3")))),
            None),
          ELet("x5", EBinOp("*", ENum(42), ENum(100), Sta),
            ELet("x6", EBinOp("+", ENum(3), ENum(2), Sta),
              ELet("x7", EBinOp("+", EVar("x5"), EVar("x6"), Sta),
                ELet("x8", EBinOp("/", EVar("x7"), EVar("x5"), Sta), EVar("x8"))))))),
      Set("fun-inline", "cse"))

    testEvalSurface(src,
      vcode(
        ELet("x5", EBinOp("*", ENum(42), ENum(100), Sta),
          ELet("x6", EBinOp("+", ENum(3), ENum(2), Sta),
            ELet("x7", EBinOp("+", EVar("x5"), EVar("x6"), Sta),
              ELet("x8", EBinOp("/", EVar("x7"), EVar("x5"), Sta), EVar("x8")))))),
      Set("fun-inline", "cse", "dce"))

    testEvalSurface(src,
      vcode(
        ELet("x3",
          ELam("x0", None,
            ELet("x1", EBinOp("+", EVar("x0"), ENum(2), Sta),
              ELet("x2", EBinOp("+", ENum(4200), EVar("x1"), Sta), EVar("x2"))),
            None),
          ENum(1))),
      Set("fun-inline", "cse", "rewriting"))

    testEvalSurface(src, vcode(ENum(1)), Set("fun-inline", "cse", "rewriting", "dce"))
  }

  test("cse-1") {
    val src = "(lift[2](2) *@2 lift[2](3)) +@2 (lift[2](2) *@2 lift[2](3))"
    testEvalSurface(src,
      vcode(ELet("x0", EBinOp("*", ENum(2), ENum(3), Sta),
        ELet("x1", EBinOp("+", EVar("x0"), EVar("x0"), Sta), EVar("x1")))),
      Set("cse"))
  }

  test("cse-2") {
    val src = "((lift[2](2) *@2 lift[2](3)) +@2 (lift[2](2) *@2 lift[2](3))) /@2 ((lift[2](2) *@2 lift[2](3)) +@2 (lift[2](2) *@2 lift[2](3)))"
    testEvalSurface(src,
      vcode(
        ELet("x0", EBinOp("*", ENum(2), ENum(3), Sta),
          ELet("x1", EBinOp("+", EVar("x0"), EVar("x0"), Sta),
            ELet("x2", EBinOp("/", EVar("x1"), EVar("x1"), Sta), EVar("x2"))))),
      Set("cse"))
  }

  test("cse-lam-1") {
    val src = """
      let f = lift[2](fun(y: Int @ 2) =>
        let z1 = lift[2](2) *@2 lift[2](3) in
        let z2 = lift[2](2) *@2 lift[2](3) in
        y +@2 z2) in
      let x1 = lift[2](2) *@2 lift[2](3) in
      f(lift[2](3))@2
    """
    testEvalSurface(src,
      vcode(
        ELet("x3",
          ELam("x0", None,
            ELet("x1", EBinOp("*", ENum(2), ENum(3), Sta),
              ELet("x2", EBinOp("+", EVar("x0"), EVar("x1"), Sta), EVar("x2"))),
            None),
          ELet("x4", EBinOp("*", ENum(2), ENum(3), Sta),
            ELet("x5", EApp(EVar("x3"), ENum(3), Sta), EVar("x5"))))),
      Set("cse"))
  }

  test("cse-lam-2") {
    val src = """
      let x1 = lift[2](2) *@2 lift[2](3) in
      let f = lift[2](fun(y: Int @ 2) =>
        let z1 = lift[2](2) *@2 lift[2](3) in
        let z2 = lift[2](2) *@2 lift[2](3) in
        y +@2 z2) in
      f(lift[2](3))@2
    """
    testEvalSurface(src,
      vcode(
        ELet("x0", EBinOp("*", ENum(2), ENum(3), Sta),
          ELet("x3",
            ELam("x1", None,
              ELet("x2", EBinOp("+", EVar("x1"), EVar("x0"), Sta), EVar("x2")),
              None),
            ELet("x4", EApp(EVar("x3"), ENum(3), Sta), EVar("x4"))))),
      Set("cse"))
  }

  test("cse-cond-1") {
    val src = "if@2 lift[2](1) ==@2 lift[2](2) then lift[2](2) *@2 lift[2](3) else lift[2](2) *@2 lift[2](3)"
    testEvalSurface(src,
      vcode(
        ELet("x0", EBinOp("==", ENum(1), ENum(2), Sta),
          ELet("x3",
            ECond(EVar("x0"),
              ELet("x1", EBinOp("*", ENum(2), ENum(3), Sta), EVar("x1")),
              ELet("x2", EBinOp("*", ENum(2), ENum(3), Sta), EVar("x2")),
              Sta),
            EVar("x3")))),
      Set("cse"))
  }

  test("cse-cond-2") {
    val src = "let x0 = lift[2](2) *@2 lift[2](3) in if@2 lift[2](1) ==@2 lift[2](2) then lift[2](2) *@2 lift[2](3) else lift[2](2) *@2 lift[2](3)"
    testEvalSurface(src,
      vcode(
        ELet("x0", EBinOp("*", ENum(2), ENum(3), Sta),
          ELet("x1", EBinOp("==", ENum(1), ENum(2), Sta),
            ELet("x2", ECond(EVar("x1"), EVar("x0"), EVar("x0"), Sta), EVar("x2"))))),
      Set("cse"))
  }

  test("cond-simp-1") {
    val src1 = "if@2 lift[2](1) ==@2 lift[2](2) then lift[2](3) *@2 lift[2](4) else lift[2](4) *@2 lift[2](5)"
    val src2 = "if@2 lift[2](2) ==@2 lift[2](2) then lift[2](3) *@2 lift[2](4) else lift[2](4) *@2 lift[2](5)"
    testEvalSurface(src1, vcode(ENum(20)), Set("rewriting", "simp-cond"))
    testEvalSurface(src2, vcode(ENum(12)), Set("rewriting", "simp-cond"))
  }

  test("cond-simp-2") {
    val src1 = """
      lift[2](fun(y: Int @ 2) =>
        let z1 = lift[2](2) *@2 lift[2](3) in
        if@2 z1 ==@2 lift[2](6)
        then y *@2 lift[2](4)
        else y *@2 (y +@2 lift[2](4)))
    """
    val src2 = """
      lift[2](fun(y: Int @ 2) =>
        let z1 = lift[2](2) *@2 lift[2](3) in
        if@2 z1 ==@2 lift[2](7)
        then y *@2 lift[2](4)
        else y *@2 (y +@2 lift[2](4)))
    """

    testEvalSurface(src1,
      vcode(
        ELet("x5",
          ELam("x0", None,
            ELet("x4", EBinOp("*", EVar("x0"), ENum(4), Sta), EVar("x4")),
            None),
          EVar("x5"))),
      Set("rewriting", "simp-cond"))

    testEvalSurface(src2,
      vcode(
        ELet("x6",
          ELam("x0", None,
            ELet("x4", EBinOp("+", EVar("x0"), ENum(4), Sta),
              ELet("x5", EBinOp("*", EVar("x0"), EVar("x4"), Sta), EVar("x5"))),
            None),
          EVar("x6"))),
      Set("rewriting", "simp-cond"))
  }
}
