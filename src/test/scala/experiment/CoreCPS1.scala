package instar.experiment.imp.cps1

import instar.experiment.*

class CoreCPS1Test extends munit.FunSuite:
  import Stage.*
  import Expr.*
  import Value.*

  val e1 = EApp2(
    ELift(ELam("x", EBinOp2("+", EVar("x"), ELift(ENum(1))))),
    ELift(ENum(41))
  )

  val e2 = ELift(
    ELam("x", EBinOp2("+", EVar("x"), ELift(ENum(1))))
  )

  val e3 = ELift(
    ELam("y", EBinOp2("*", EVar("y"), ELift(ENum(42))))
  )

  val e4 = ECond(
    ELift(EBool(true)),
    EApp2(e2, ELift(ENum(10))),
    EApp2(e3, ELift(ENum(20))),
    Dyn
  )

  def testEval(e: Expr, str: String): Unit =
    assertEquals(eval(e).toString, str)

  test("lam-app"):
    testEval(e1,
      "VCode(ELet(x3,ELam(x0,ELet(x1,ENum(1),ELet(x2,EBinOp(+,EVar(x0),EVar(x1),Sta),EVar(x2)))),ELet(x4,ENum(41),ELet(x5,EApp(EVar(x3),EVar(x4),Sta),EVar(x5)))))")
    testEval(e2,
      "VCode(ELet(x3,ELam(x0,ELet(x1,ENum(1),ELet(x2,EBinOp(+,EVar(x0),EVar(x1),Sta),EVar(x2)))),EVar(x3)))")

  test("cond"):
    testEval(e4,
      "VCode(ELet(x0,EBool(true),ELet(x13,ECond(EVar(x0),ELet(x4,ELam(x1,ELet(x2,ENum(1),ELet(x3,EBinOp(+,EVar(x1),EVar(x2),Sta),EVar(x3)))),ELet(x5,ENum(10),ELet(x6,EApp(EVar(x4),EVar(x5),Sta),EVar(x6)))),ELet(x10,ELam(x7,ELet(x8,ENum(42),ELet(x9,EBinOp(*,EVar(x7),EVar(x8),Sta),EVar(x9)))),ELet(x11,ENum(20),ELet(x12,EApp(EVar(x10),EVar(x11),Sta),EVar(x12)))),Sta),EVar(x13))))")

  test("run"):
    testEval(ENum(1), "VNum(1)")
    testEval(ERun(ELift(ENum(1))), "VNum(1)")

    testEval(e2,
      "VCode(ELet(x3,ELam(x0,ELet(x1,ENum(1),ELet(x2,EBinOp(+,EVar(x0),EVar(x1),Sta),EVar(x2)))),EVar(x3)))")
    testEval(ERun(e2),
      "VClo(x0,ELet(x1,ENum(1),ELet(x2,EBinOp(+,EVar(x0),EVar(x1),Sta),EVar(x2))),Map())")

    val e2App = ELet("y", e2, EApp2(EVar("y"), ELift(ENum(1))))
    testEval(e2App,
      "VCode(ELet(x3,ELam(x0,ELet(x1,ENum(1),ELet(x2,EBinOp(+,EVar(x0),EVar(x1),Sta),EVar(x2)))),ELet(x4,ENum(1),ELet(x5,EApp(EVar(x3),EVar(x4),Sta),EVar(x5)))))")
    testEval(ERun(e2App), "VNum(2)")
