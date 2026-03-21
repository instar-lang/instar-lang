package instar.interp

import instar.parser.Parser
import instar.syntax.*
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
      case EPrimOp(op, rands, st) => EPrimOp(op, rands.map(normalizeExpr), st)
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

class SurfaceCoreEffAnalysis extends SurfaceBase {
  test("is-app-1") {
    val src = """
    let app = lift[1](fun(x: Int @ 1) => x)(lift[1](42))@1 in
    if isApp(app) then lift[1](true) else lift[1](false)
    """
    testEvalSurface(src,
      VCode(
        ELet("x1", ELam("x0", None, EVar("x0"), None),
          ELet("x2", EApp(EVar("x1"), ENum(42), Sta), EBool(true)))))
  }

  test("is-app-2") {
    testEvalSurface("isApp(lift[1](42))", VBool(false))
  }

  test("is-app-conflict") {
    val src = "lift[1](isApp(lift[1](fun(x: Int @ 1) => x)(lift[1](42))@1))"
    testEvalSurface(src,
      VCode(
        ELet("x1", ELam("x0", None, EVar("x0"), None),
          ELet("x2", EApp(EVar("x1"), ENum(42), Sta), EBool(true)))),
      Set("dce"))
    testEvalSurface(src, VCode(EBool(false)), Set("fun-inline", "dce"))
  }
}

class SurfaceCoreEffTest extends SurfaceBase {
  private val lamAddSrc = "lift[1](fun(x: Int @ 1) => x +@1 lift[1](1))"
  private val lamMulSrc = "lift[1](fun(y: Int @ 1) => y *@1 lift[1](42))"
  private val lamAddBody = ELet("x1", EBinOp("+", EVar("x0"), ENum(1), Sta), EVar("x1"))
  private val lamAddCode = ELet("x2", ELam("x0", None, lamAddBody, None), EVar("x2"))
  private val lamMulBody = ELet("x5", EBinOp("*", EVar("x4"), ENum(42), Sta), EVar("x5"))
  private val lamMulCode = ELet("x6", ELam("x4", None, lamMulBody, None), EVar("x6"))

  test("lam-app") {
    testEvalSurface(s"$lamAddSrc(lift[1](41))@1",
      VCode(ELet("x2", ELam("x0", None, lamAddBody, None),
        ELet("x3", EApp(EVar("x2"), ENum(41), Sta), EVar("x3")))))
    testEvalSurface(lamAddSrc,
      VCode(lamAddCode))
  }

  test("cond") {
    val src = s"if@1 lift[1](true) then $lamAddSrc(lift[1](10))@1 else $lamMulSrc(lift[1](20))@1"
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
    testEvalSurface("(sfun[s] => lift[s](fun(x: Int @ s) => x +@s lift[s](1))(lift[s](5))@s)[0]", VNum(6))
    testEvalSurface("(sfun[s] => lift[s](fun(x: Int @ s) => x +@s lift[s](1))(lift[s](5))@s)[1]",
      VCode(ELet("x2", ELam("x0", None, lamAddBody, None),
        ELet("x3", EApp(EVar("x2"), ENum(5), Sta), EVar("x3")))))
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
      in power[0](2)(3)
    """

    val codeSrc = """
      letrec power: forall[s]. Int @ s -> Int -> Int @ s =
        sfun[s] => fun(x: Int @ s) => fun(n: Int): Int @ s =>
          if n == 0 then lift[s](1) else x *@s power[s](x)(n - 1)
      in lift[1](fun(x: Code[Int]): Code[Int] => power[1](x)(3))
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
      letrec impPower: forall[s]. Int @ s -> Int -> Ref[Int] -> Int @ s =
        sfun[s] => fun(b: Int @ s) => fun(n: Int) => fun(result: Ref[Int]): Int @ s =>
          if n == 0 then deref@s(result) else let _ = assign@s(result, b *@s deref@s(result)) in impPower[s](b)(n - 1)(result)
      in impPower[0](2)(3)(ref(1))
    """
    val codeSrc = """
      letrec impPower: forall[s]. Int @ s -> Int -> Ref[Int] -> Int @ s =
        sfun[s] => fun(b: Int @ s) => fun(n: Int) => fun(result: Ref[Int]): Int @ s =>
          if n == 0 then deref@s(result) else let _ = assign@s(result, b *@s deref@s(result)) in impPower[s](b)(n - 1)(result)
      in lift[1](fun(x: Code[Int]): Code[Int] => impPower[1](x)(3)(ref@1(lift[1](1))))
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

  test("stuck") {
    intercept[RuntimeException] {
      eval(Parser.parse("let x = ref@1(lift[1](0)) in 10"))
    }
  }

  test("fix-fib") {
    val src = "let fib = fix[0] fib. fun(n: Int): Int => if n <= 1 then 1 else n * fib(n - 1) in fib(5)"
    testEvalSurface(src, VNum(120))
  }

  test("letrec-fib") {
    val src = "letrec fib: Int -> Int = fun(n: Int) => if n <= 1 then 1 else n * fib(n - 1) in fib(5)"
    testEvalSurface(src, VNum(120))
  }

  test("fix-second-stage") {
    val src =
      "let fib = fix[1] fib. " +
      "lift[1](fun(n: Code[Int]): Code[Int] => " +
      "if@1 n <=@1 lift[1](1) then lift[1](1) else n *@1 fib(n -@1 lift[1](1))@1) " +
      "in fib(lift[1](5))@1"
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
    testEvalSurface("lift[1](ref@0(42))", VCode(ELet("x0", ELoc(0), EVar("x0"))))
  }

  test("lift-curry-lam") {
    val src = "lift[1](fun(x: Int @ 1) => lift[1](fun(y: Int @ 1) => x +@1 y))"
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
    testEvalSurface("run(lift[1](1))", VNum(1))
    testEvalSurface(lamAddSrc, VCode(lamAddCode))
    testEvalSurface(s"run($lamAddSrc)", VClo("x0", None, lamAddBody, None, Map(), Map()))

    val appSrc = s"let y = $lamAddSrc in y(lift[1](1))@1"
    testEvalSurface(appSrc,
      VCode(ELet("x2", ELam("x0", None, lamAddBody, None),
        ELet("x3", EApp(EVar("x2"), ENum(1), Sta), EVar("x3")))))

    testEvalSurface("deref(run(lift[1](ref@0(1))))", VNum(1))
  }
}
