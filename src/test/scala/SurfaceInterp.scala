package instar.interp

import instar.parser.parse
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
    val (value, _) = eval(parse(src))
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

  test("comma-separated let stage binders") {
    val src = "let f[s1, s2] = fun@s1(x: Int @ s2) => x in f[1][1](2)"
    testEvalSurface(src, VNum(2))
  }

  test("comma-separated stage application") {
    val src = "let f[s1, s2] = fun@s1(x: Int @ s2) => x in f[1, 1](2)"
    testEvalSurface(src, VNum(2))
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
      eval(parse("let x = ref@2(lift[2](0)) in 10"))
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

class ADT extends SurfaceBase {
  test("list-length") {
    val src = """
      type List[A] = Nil | Cons(A, List[A]) in
      let length = fix go. fun(xs: List[A]) =>
        match xs with
        | Nil => 0
        | Cons(_, ys) => 1 + go(ys)
      in
      length(Cons(1, Cons(2, Cons(3, Nil))))
    """
    testEvalSurface(src, VNum(3))
  }

  test("tree-size") {
    val src = """
      type Tree[A] = Leaf | Node(Tree[A], A, Tree[A]) in
      let size = fix go. fun(t: Tree[A]) =>
        match t with
        | Leaf => 0
        | Node(l, _, r) => 1 + go(l) + go(r)
      in
      size(Node(Node(Leaf, 1, Leaf), 2, Leaf))
    """
    testEvalSurface(src, VNum(2))
  }

  test("option-get-or-else") {
    val src = """
      type Option[A] = None | Some(A) in
      let getOrElse = fun(o: Option[Int]) => fun(d: Int) =>
        match o with
        | None => d
        | Some(x) => x
      in
      getOrElse(Some(42))(0)
    """
    testEvalSurface(src, VNum(42))
  }

  test("list-length with a stage parameter") {
    val src = """
      type List[A, s] = Nil | Cons(A@s, List[A, s]) in
      let length = fix go. fun(xs: List[A]) =>
        match xs with
        | Nil => 0
        | Cons(_, ys) => 1 + go(ys)
      in
      length(Cons(1, Cons(2, Cons(3, Nil))))
    """
    testEvalSurface(src, VNum(3))
  }
}

/** §5.2 staged streams, core data structures. */
trait Stream52Base extends SurfaceBase {
  // LMS: (R[IntRef], R[Array[α]]) as of_arr's state.
  protected val pairDecl: String =
    "type Pair[A, B] = Pair(A, B) in"

  // LMS:
  //   sealed trait stream_shape[+α, +ζ]
  //   case object Nil
  //   case class Cons[α, ζ](a: α, rest: ζ)
  protected val streamShapeDecl: String =
    "type StreamShape[A, B] = Nil | Cons(A, B) in"

  // LMS:
  //   trait st_stream[R[+_], α] {
  //     type σ
  //     def init[ω](k: σ => R[ω]): R[ω]
  //     def step[ω](s: σ)(k: stream_shape[R[α], Unit] => R[ω]): R[ω]
  //   }
  // Instar: ∃S. init × step, with R[α] = α @ s.
  protected val stStreamDecl: String = """
    type StStream[A, s] = StStream(
      exists[S]. Pair[
        (forall[W]. (S -> W @ s) -> W @ s),
        (forall[W]. S -> (StreamShape[A @ s, Unit] -> W @ s) -> W @ s)
      ]
    ) in
  """

  // LMS:
  //   def incr[R[+_]](r: R[IntRef]): R[Unit]
  protected val incrDecl: String = """
  let incr[s](r: Ref[Int] @ s): Unit @ s =
    r :=@s (!@s r +@s lift[s](1)) in
  """

  // LMS:
  /*
  def of_arr[R[+_], α: Manifest](arr: R[Array[α]]): st_stream[R, α] =
    new st_stream[R, α] {
      type σ = (R[IntRef], R[Array[α]])

      def init[ω: Manifest](k: σ => R[ω]): R[ω] = k((ref[R](0), arr))

      def step[ω: Manifest](s: σ)(k: stream_shape[R[α], Unit] => R[ω]): R[ω] = {
        val (i, a) = s
        iff[R, ω](lt[R](read[R](i), length[R, α](a))) {
          val el = at[R, α](a, read[R](i))
          incr[R](i)
          k(stream_shape.Cons(el, ()))
        } {
          k(stream_shape.Nil)
        }
      }
    }
  */
  protected val ofArrDecl: String = """
  let of_arr[A, s](arr: Array[A] @ s): StStream[A, s] =
    let init[W](k: Pair[Ref[Int] @ s, Array[A] @ s] -> W @ s): W @ s =
      k(Pair(ref@s(lift[s](0)), arr)) in

    let step[W](state: Pair[Ref[Int] @ s, Array[A] @ s])
        (k: StreamShape[A @ s, Unit] -> W @ s): W @ s =
      match state with
      | Pair(i, a) =>
        if@s (!@s i <@s len@s(a)) then
          let el = get@s(a, !@s i) in
          let _ = incr[s](i) in
          k(Cons(el, ()))
        else
          k(Nil) in

    StStream(pack [
      Pair[Ref[Int] @ s, Array[A] @ s],
      Pair(init, step)
    ]) in
  """

  // LMS:
  /*
  def map[R[+_], α: Manifest, β: Manifest](f: R[α] => R[β])(str: st_stream[R, α]): st_stream[R, β] =
    new st_stream[R, β] {
      type σ = str.σ

      def init[ω: Manifest](k: σ => R[ω]): R[ω] = str.init[ω](k)

      def step[ω: Manifest](s: σ)(k: stream_shape[R[β], Unit] => R[ω]): R[ω] =
        str.step[ω](s) {
          case stream_shape.Nil        => k(stream_shape.Nil)
          case stream_shape.Cons(a, u) => k(stream_shape.Cons(f(a), u))
        }
    }
  */
  protected val mapDecl: String = """
  let map[A, B, s](f: A @ s -> B @ s)(str: StStream[A, s]): StStream[B, s] =
    match str with
    | StStream(packed) =>
      unpack [S, repr] = packed in
      match repr with
      | Pair(init, step) =>
        let step2[W](state: S)(k: StreamShape[B @ s, Unit] -> W @ s): W @ s =
          step[W](state)(fun(shape: StreamShape[A @ s, Unit]) =>
            match shape with
            | Nil => k(Nil)
            | Cons(a, u) => k(Cons(f(a), u))) in
        StStream(pack [
          S,
          Pair(init, step2)
        ]) in
  """

  // LMS:
  /*
  def fold[R[+_], α: Manifest, ζ: Manifest](f: (R[ζ], R[α]) => R[ζ], z: R[ζ])(str: st_stream[R, α]): R[ζ] =
    str.init[ζ] { (s: str.σ) =>
      lazy val loop: R[ζ => ζ] = fun[R, ζ, ζ] { (z: R[ζ]) =>
        str.step[ζ](s) {
          case stream_shape.Nil        => z
          case stream_shape.Cons(a, _) => app[R, ζ, ζ](loop, f(z, a))
        }
      }
      app[R, ζ, ζ](loop, z)
    }
  */
  protected val foldDecl: String = """
  let fold[A, Z, s](f: Z @ s -> A @ s -> Z @ s)(z: Z @ s)(str: StStream[A, s]): Z @ s =
    match str with
    | StStream(packed) =>
      unpack [S, repr] = packed in
      match repr with
      | Pair(init, step) =>
        init[Z](fun(state: S) =>
          let loop = fix@s go. lift[s](fun(acc: Z @ s): Z @ s =>
            step[Z](state)(fun(shape: StreamShape[A @ s, Unit]) =>
              match shape with
              | Nil => acc
              | Cons(a, _) => go(f(acc)(a))@s))
          in loop(z)@s) in
  """

  // LMS:
  /*
  def sumOfSquares[R[+_]](arr: R[Array[Int]])(implicit S: Stream52Cast): R[Int] = {
    val str = S.map[R, Int, Int]((x: R[Int]) => S.times[R](x, x))(S.of_arr[R, Int](arr))
    S.fold[R, Int, Int]((z: R[Int], a: R[Int]) => S.plus[R](z, a), S.int[R](0))(str)
  }
  */
  protected val sumOfSquaresDecl: String = """
  let sumOfSquares[s]: (Array[Int] -> Int) @ s =
    lift[s](fun(arr: Array[Int] @ s): Int @ s =>
      let arr = map[Int, Int, s](fun(x: Int @ s) => x *@s x)(of_arr[Int, s](arr)) in
      let res = fold[Int, Int, s](fun(acc: Int @ s) => fun(x: Int @ s) => acc +@s x)(lift[s](0))(arr) in
      res) in
  """

  protected val iotaDecl: String = """
  let iota = fun(n: Int) =>
    let a = alloc(n, 0) in
    let loop = fix go. fun(i: Int) =>
      if i < n then let _ = set(a, i, i + 1) in go(i + 1) else a
    in
    loop(0) in
  """

  protected def stream52(decls: String*)(body: String): String =
    decls.map(_.trim).mkString("\n") + "\n" + body
}

class Stream52 extends Stream52Base {
  test("Pair is the product of two values") {
    val src = stream52(pairDecl)("""
      match Pair(1, 2) with
      | Pair(x, y) => x + y
    """)
    testEvalSurface(src, VNum(3))
  }

  test("StreamShape is Nil | Cons of the element and the rest") {
    val src = stream52(streamShapeDecl)("""
      match Cons(42, ()) with
      | Nil => 0
      | Cons(x, _) => x
    """)
    testEvalSurface(src, VNum(42))
  }

  test("of_arr yields elements in order, advances, then terminates") {
    val src = stream52(pairDecl, streamShapeDecl, stStreamDecl, incrDecl, ofArrDecl)("""
      let a = alloc(2, 0) in
      let _ = set(a, 0, 7) in
      let _ = set(a, 1, 8) in
      let str = of_arr[Int, 1](a) in
      match str with
      | StStream(packed) =>
        unpack [S, repr] = packed in
        match repr with
        | Pair(init, step) =>
          init[Int](fun(s: S) =>
            step[Int](s)(fun(shape1: StreamShape[Int, Unit]) =>
              match shape1 with
              | Nil => 0
              | Cons(x, _) =>
                step[Int](s)(fun(shape2: StreamShape[Int, Unit]) =>
                  match shape2 with
                  | Nil => x
                  | Cons(y, _) =>
                    step[Int](s)(fun(shape3: StreamShape[Int, Unit]) =>
                      match shape3 with
                      | Nil => x * 10 + y
                      | Cons(_, _) => 0))))
    """)
    testEvalSurface(src, VNum(78))
  }

  test("map transforms yielded elements") {
    val src = stream52(pairDecl, streamShapeDecl, stStreamDecl, incrDecl, ofArrDecl, mapDecl)("""
      let a = alloc(2, 0) in
      let _ = set(a, 0, 7) in
      let _ = set(a, 1, 8) in
      let str = of_arr[Int, 1](a) in
      let mapped = map[Int, Int, 1](fun(x: Int) => x + 1)(str) in
      match mapped with
      | StStream(packed) =>
        unpack [S, repr] = packed in
        match repr with
        | Pair(init, step) =>
          init[Int](fun(s: S) =>
            step[Int](s)(fun(shape1: StreamShape[Int, Unit]) =>
              match shape1 with
              | Nil => 0
              | Cons(x, _) =>
                step[Int](s)(fun(shape2: StreamShape[Int, Unit]) =>
                  match shape2 with
                  | Nil => x
                  | Cons(y, _) =>
                    step[Int](s)(fun(shape3: StreamShape[Int, Unit]) =>
                      match shape3 with
                      | Nil => x * 10 + y
                      | Cons(_, _) => 0))))
    """)
    testEvalSurface(src, VNum(89))
  }

  test("sum of squares at stage 1") {
    val src = stream52(
      pairDecl,
      streamShapeDecl,
      stStreamDecl,
      incrDecl,
      ofArrDecl,
      mapDecl,
      foldDecl,
      sumOfSquaresDecl,
      iotaDecl,
    )("""
      let a = iota(10) in
      sumOfSquares[1](a)
    """)
    testEvalSurface(src, VNum(385))
  }

  test("stage-2 sum of squares fuses") {
    val src = stream52(
      pairDecl,
      streamShapeDecl,
      stStreamDecl,
      incrDecl,
      ofArrDecl,
      mapDecl,
      foldDecl,
      sumOfSquaresDecl,
    )("""
      sumOfSquares[2]
    """)
    val (value, _) = eval(parse(src))
    val code = instar.pretty.value(value)
    // LMS (Stream52Suite / Stream52CastSuite, §5.2):
    /*
    class Snippet() extends (Array[Int] => Int) {
      def apply(x0: Array[Int]): Int = {
        var x1: scala.runtime.IntRef = null.asInstanceOf[scala.runtime.IntRef]
        var x2: Function1[Int, Int] = null.asInstanceOf[Function1[Int, Int]]
        var x3: Int = null.asInstanceOf[Int]
        x1 = new scala.runtime.IntRef(0)
        x2 = x4
        x3 = x0.length
        def x4(x5: Int): Int = if (x1.elem < x3) {
          val x6 = x0(x1.elem)
          x1.elem = (x1.elem + 1)
          x2(x5 + x6 * x6)
        } else x5
        x4(0)
      }
    }
    */
    val expected =
      """|let x19 (x0) =
         |  let x1 = ref(0) in
         |  let x17 = fix f2.
         |    let x16 (x3) =
         |      let x4 = ! x1 in
         |      let x5 = len(x0) in
         |      let x6 = x4 < x5 in
         |      let x15 = if x6 then
         |        let x7 = ! x1 in
         |        let x8 = get(x0, x7) in
         |        let x9 = ! x1 in
         |        let x10 = x9 + 1 in
         |        let x11 = x1 := x10 in
         |        let x12 = x8 * x8 in
         |        let x13 = x3 + x12 in
         |        let x14 = f2 x13 in x14
         |      else
         |        x3
         |      in x15
         |    in x16
         |  in
         |  let x18 = x17 0 in x18
         |in x19""".stripMargin
    assertEquals(code, expected)
  }

  test("stage-2 sum of squares runs on an array") {
    val src = stream52(
      pairDecl,
      streamShapeDecl,
      stStreamDecl,
      incrDecl,
      ofArrDecl,
      mapDecl,
      foldDecl,
      sumOfSquaresDecl,
      iotaDecl,
    )("""
      let a = iota(10) in
      let squares = run(sumOfSquares[2]) in
      squares(a)
    """)
    testEvalSurface(src, VNum(385))
  }
}
