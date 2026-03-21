package instar.eff

import Stage.*
import Expr.*
import Type.*
import Value.*

class CoreEffTest extends munit.FunSuite {

  val e1 = EApp2(
    ELift2(
      ELam("x", None, EBinOp2("+", EVar("x"), ELift2(ENum(1))), None)
    ),
    ELift2(ENum(41)),
  )

  val e2 = ELift2(ELam("x", None, EBinOp2("+", EVar("x"), ELift2(ENum(1))), None))

  val e3 = ELift2(ELam("y", None, EBinOp2("*", EVar("y"), ELift2(ENum(42))), None))

  val e4 = ECond(
    ELift2(EBool(true)),
    EApp2(e2, ELift2(ENum(10))),
    EApp2(e3, ELift2(ENum(20))),
    Dyn
  )

  def e5(stage: Int) = {
    // (Λs. (λx. x +ˢ 1ˢ)ˢ 5ˢ)[stage]
    val f = ESLam("s", EApp(
      ELift(ELam("x", None, EBinOp("+", EVar("x"), ELift(ENum(1), SVar("s")), SVar("s")), None), SVar("s")),
      ELift(ENum(5), SVar("s")),
      SVar("s")
    ))
    val arg = SNum(stage)
    ESApp(f, arg)
  }

  val e6 = ELetRec(
    "fact",
    TFun(TInt, TInt),
    ELam("n", Some(TInt), ECond1(
      EBinOp1("<=", EVar("n"), ENum(1)),
      ENum(1),
      EBinOp1("*",
        EVar("n"),
        EApp1(EVar("fact"), EBinOp1("-", EVar("n"), ENum(1)))),
    ), Some(TInt)),
    EApp1(EVar("fact"), ENum(5))
  )

  val e7 = ELetRec(
    "power",
    TFun(TInt, TFun(TInt, TInt)),
    ELam("x", Some(TInt), ELam("n", Some(TInt), ECond1(
      EBinOp1("==", EVar("n"), ENum(0)),
      ENum(1),
      EBinOp1("*",
        EVar("x"),
        EApp1(EApp1(EVar("power"), EVar("x")), EBinOp1("-", EVar("n"), ENum(1)))),
    ), Some(TInt)), Some(TInt)),
    EApp1(EApp1(EVar("power"), ENum(2)), ENum(10))
  )

  def e8(body: Expr) = ELetRec(
    "power",
    TForallSt("s", TFun(TAt(TInt, SVar("s")), TFun(TInt, TAt(TInt, SVar("s"))))),
    ESLam("s",
      ELam("x", Some(TAt(TInt, SVar("s"))), ELam("n", Some(TInt), ECond1(
        EBinOp1("==", EVar("n"), ENum(0)),
        ELift(ENum(1), SVar("s")),
        EBinOp("*",
          EVar("x"),
          EApp1(EApp1(ESApp(EVar("power"), SVar("s")), EVar("x")), EBinOp1("-", EVar("n"), ENum(1))), SVar("s")),
      ), Some(TAt(TInt, SVar("s")))), Some(TInt))),
    body
  )

  /*
    def impPower[s](b: Intˢ, n: Int, result: Ref[Int]ˢ): Intˢ =
      if n == 0 then
        !ˢresult
      else
        result :=ˢ b *ˢ !ˢresult
        impPower(b, n - 1, result)
  */

  def e9(body: Expr) = ELetRec(
    "impPower",
    TForallSt("s", TFun(TAt(TInt, SVar("s")), TFun(TInt, TFun(TRef(TInt), TAt(TInt, SVar("s")))))),
    ESLam("s",
      ELam("b", Some(TAt(TInt, SVar("s"))),
        ELam("n", Some(TInt),
          ELam("result", Some(TRef(TInt)),
            ECond1(
              EBinOp1("==", EVar("n"), ENum(0)),
              EDeref(EVar("result"), SVar("s")),
              ELet("_", EAssign(EVar("result"), EBinOp("*", EVar("b"), EDeref(EVar("result"), SVar("s")), SVar("s")), SVar("s")),
                EApp1(EApp1(EApp1(ESApp(EVar("impPower"), SVar("s")), EVar("b")), EBinOp1("-", EVar("n"), ENum(1))), EVar("result")))),
          Some(TAt(TInt, SVar("s")))), Some(TFun(TAt(TRef(TInt), SVar("s")), TAt(TInt, SVar("s"))))), Some(TAt(TInt, SVar("s"))))),
    body
  )

  val e10 = {
    val fib = EFix("fib", ELam("n", Some(TInt),
      ECond1(
        EBinOp1("<=", EVar("n"), ENum(1)),
        ENum(1),
        EBinOp1("*",
          EVar("n"),
          EApp1(EVar("fib"), EBinOp1("-", EVar("n"), ENum(1)))),
      ), Some(TInt)), Sta)
    ELet("fib", fib, EApp1(EVar("fib"), ENum(5)))
  }

  val e11 = {
    val fib = EFix("fib", ELift2(ELam("n", Some(TCode(TInt)),
      ECond2(
        EBinOp2("<=", EVar("n"), ELift2(ENum(1))),
        ELift2(ENum(1)),
        EBinOp2("*",
          EVar("n"),
          EApp2(EVar("fib"), EBinOp2("-", EVar("n"), ELift2(ENum(1))))),
      ), Some(TCode(TInt)))), Dyn)
    ELet("fib", fib, EApp2(EVar("fib"), ELift2(ENum(5))))
  }

  def testEval(e: Expr, str: String): Unit =
    val (v, _) = eval(e)
    assertEquals(v.toString, str)

  test("lam-app") {
    testEval(e1, "VCode(ELet(x2,ELam(x0,None,ELet(x1,EBinOp(+,EVar(x0),ENum(1),SNum(0)),EVar(x1)),None),ELet(x3,EApp(EVar(x2),ENum(41),SNum(0)),EVar(x3))))")

    testEval(e2, "VCode(ELet(x2,ELam(x0,None,ELet(x1,EBinOp(+,EVar(x0),ENum(1),SNum(0)),EVar(x1)),None),EVar(x2)))")
  }

  test("cond") {
    testEval(e4, "VCode(ELet(x8,ECond(EBool(true),ELet(x2,ELam(x0,None,ELet(x1,EBinOp(+,EVar(x0),ENum(1),SNum(0)),EVar(x1)),None),ELet(x3,EApp(EVar(x2),ENum(10),SNum(0)),EVar(x3))),ELet(x6,ELam(x4,None,ELet(x5,EBinOp(*,EVar(x4),ENum(42),SNum(0)),EVar(x5)),None),ELet(x7,EApp(EVar(x6),ENum(20),SNum(0)),EVar(x7))),SNum(0)),EVar(x8)))")
  }

  test("stage-poly") {
    testEval(e5(0), "VNum(6)")

    testEval(e5(1), "VCode(ELet(x2,ELam(x0,None,ELet(x1,EBinOp(+,EVar(x0),ENum(1),SNum(0)),EVar(x1)),None),ELet(x3,EApp(EVar(x2),ENum(5),SNum(0)),EVar(x3))))")

    val (VCode(e), _) = eval(e5(1))
    testEval(e, "VNum(6)")
  }

  test("rec") {
    testEval(e6, "VNum(120)")
    testEval(e7, "VNum(1024)")
  }

  test("rec-stage-poly") {
    testEval(e8(EApp1(EApp1(ESApp(EVar("power"), SNum(0)), ENum(2)), ENum(3))), "VNum(8)")

    testEval(e8(ELift2(ELam("x", Some(TCode(TInt)), EApp1(EApp1(ESApp(EVar("power"), SNum(1)), EVar("x")), ENum(3)), Some(TCode(TInt))))),
      "VCode(ELet(x4,ELam(x0,Some(TInt),ELet(x1,EBinOp(*,EVar(x0),ENum(1),SNum(0)),ELet(x2,EBinOp(*,EVar(x0),EVar(x1),SNum(0)),ELet(x3,EBinOp(*,EVar(x0),EVar(x2),SNum(0)),EVar(x3)))),Some(TInt)),EVar(x4)))")

    val (VCode(e), _) = eval(e8(ELift2(ELam("x", Some(TCode(TInt)), EApp1(EApp1(ESApp(EVar("power"), SNum(1)), EVar("x")), ENum(3)), Some(TCode(TInt))))))
    testEval(EApp1(e, ENum(2)), "VNum(8)")
  }

  test("rec-imp-stage-poly") {
    testEval(e9(EApp1(EApp1(EApp1(ESApp(EVar("impPower"), SNum(0)), ENum(2)), ENum(3)), EAlloc1(ENum(1)))), "VNum(8)")

    testEval(e9(ELift2(ELam("x", Some(TCode(TInt)), EApp1(EApp1(EApp1(ESApp(EVar("impPower"), SNum(1)), EVar("x")), ENum(3)), EAlloc2(ELift2(ENum(1)))), Some(TCode(TInt))))),
      "VCode(ELet(x12,ELam(x0,Some(TInt),ELet(x1,EAlloc(ENum(1),SNum(0)),ELet(x2,EDeref(EVar(x1),SNum(0)),ELet(x3,EBinOp(*,EVar(x0),EVar(x2),SNum(0)),ELet(x4,EAssign(EVar(x1),EVar(x3),SNum(0)),ELet(x5,EDeref(EVar(x1),SNum(0)),ELet(x6,EBinOp(*,EVar(x0),EVar(x5),SNum(0)),ELet(x7,EAssign(EVar(x1),EVar(x6),SNum(0)),ELet(x8,EDeref(EVar(x1),SNum(0)),ELet(x9,EBinOp(*,EVar(x0),EVar(x8),SNum(0)),ELet(x10,EAssign(EVar(x1),EVar(x9),SNum(0)),ELet(x11,EDeref(EVar(x1),SNum(0)),EVar(x11)))))))))))),Some(TInt)),EVar(x12)))")

    val (VCode(e), _) = eval(e9(ELift2(ELam("x", Some(TCode(TInt)), EApp1(EApp1(EApp1(ESApp(EVar("impPower"), SNum(1)), EVar("x")), ENum(3)), EAlloc2(ELift2(ENum(1)))), Some(TCode(TInt))))))
    testEval(EApp1(e, ENum(2)), "VNum(8)")
  }

  test("stuck") {
    intercept[RuntimeException] {
      // The interpreter doesn't allow discarding a second-stage term
      val e = ELet("x", EAlloc2(ELift2(ENum(0))), ENum(10))
      eval(e)
    }
  }

  test("fix") {
    testEval(e10, "VNum(120)")
  }

  test("fix-second-stage") {
    testEval(e11,
      "VCode(ELet(x8,EFix(f0,ELet(x7,ELam(x1,Some(TInt),ELet(x2,EBinOp(<=,EVar(x1),ENum(1),SNum(0)),ELet(x6,ECond(EVar(x2),ENum(1),ELet(x3,EBinOp(-,EVar(x1),ENum(1),SNum(0)),ELet(x4,EApp(EVar(f0),EVar(x3),SNum(0)),ELet(x5,EBinOp(*,EVar(x1),EVar(x4),SNum(0)),EVar(x5)))),SNum(0)),EVar(x6))),Some(TInt)),EVar(x7)),SNum(0)),ELet(x9,EApp(EVar(x8),ENum(5),SNum(0)),EVar(x9))))")

    val (VCode(e), _) = eval(e11)
    testEval(e, "VNum(120)")
  }

  test("lift-loc") {
    val e = ELift2(EAlloc1(ENum(42)))
    testEval(e, "VCode(ELet(x0,ELoc(0),EVar(x0)))")
  }

  test("lift-curry-lam") {
    val e = ELift2(ELam("x", None, ELift2(ELam("y", None, EBinOp2("+", EVar("x"), EVar("y")), None)), None))
    val exp = """
    VCode(ELet(x4,
      ELam(x0,None,
        ELet(x3,
          ELam(x1,None,
            ELet(x2,EBinOp(+,EVar(x0),EVar(x1),SNum(0)),EVar(x2)),None),
        EVar(x3)),None),
      EVar(x4)))
    """.stripMargin.replaceAll("\n", "").replaceAll(" ", "")
    testEval(e, exp)
  }

  test("run") {
    testEval(ENum(1), "VNum(1)")

    testEval(ERun(ELift2(ENum(1))), "VNum(1)")

    val e1 =
      ELift2(ELam("x", None, EBinOp2("+", EVar("x"), ELift2(ENum(1))), None))

    testEval(
      e1,
      "VCode(ELet(x2,ELam(x0,None,ELet(x1,EBinOp(+,EVar(x0),ENum(1),SNum(0)),EVar(x1)),None),EVar(x2)))"
    )

    testEval(
      ERun(e1),
      "VClo(x0,None,ELet(x1,EBinOp(+,EVar(x0),ENum(1),SNum(0)),EVar(x1)),None,Map(),Map())"
    )

    val e2 = ELet(
      "y",
      ELift2(ELam("x", None, EBinOp2("+", EVar("x"), ELift2(ENum(1))), None)),
      EApp2(EVar("y"), ELift2(ENum(1)))
    )

    testEval(
      e2,
      "VCode(ELet(x2,ELam(x0,None,ELet(x1,EBinOp(+,EVar(x0),ENum(1),SNum(0)),EVar(x1)),None),ELet(x3,EApp(EVar(x2),ENum(1),SNum(0)),EVar(x3))))"
    )

    testEval(
      ERun(e2),
      "VNum(2)"
    )

    val e3 = EDeref1(ERun(ELift2(EAlloc1(ENum(1)))))

    testEval(
      e3,
      "VNum(1)"
    )
  }
}
