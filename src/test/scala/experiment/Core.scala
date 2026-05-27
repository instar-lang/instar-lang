package instar.experiment.noeff

import instar.experiment.*

class CoreTest extends munit.FunSuite:
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
      "VCode(ELet(x2,ELam(x0,ELet(x1,EBinOp(+,EVar(x0),ENum(1),Sta),EVar(x1))),ELet(x3,EApp(EVar(x2),ENum(41),Sta),EVar(x3))))")
    testEval(e2,
      "VCode(ELet(x2,ELam(x0,ELet(x1,EBinOp(+,EVar(x0),ENum(1),Sta),EVar(x1))),EVar(x2)))")

  test("cond"):
    testEval(e4,
      "VCode(ELet(x8,ECond(EBool(true),ELet(x2,ELam(x0,ELet(x1,EBinOp(+,EVar(x0),ENum(1),Sta),EVar(x1))),ELet(x3,EApp(EVar(x2),ENum(10),Sta),EVar(x3))),ELet(x6,ELam(x4,ELet(x5,EBinOp(*,EVar(x4),ENum(42),Sta),EVar(x5))),ELet(x7,EApp(EVar(x6),ENum(20),Sta),EVar(x7))),Sta),EVar(x8)))")

  test("run"):
    testEval(ENum(1), "VNum(1)")
    testEval(ERun(ELift(ENum(1))), "VNum(1)")

    testEval(e2,
      "VCode(ELet(x2,ELam(x0,ELet(x1,EBinOp(+,EVar(x0),ENum(1),Sta),EVar(x1))),EVar(x2)))")
    testEval(ERun(e2),
      "VClo(x0,ELet(x1,EBinOp(+,EVar(x0),ENum(1),Sta),EVar(x1)),Map())")

    val e2App = ELet("y", e2, EApp2(EVar("y"), ELift(ENum(1))))
    testEval(e2App,
      "VCode(ELet(x2,ELam(x0,ELet(x1,EBinOp(+,EVar(x0),ENum(1),Sta),EVar(x1))),ELet(x3,EApp(EVar(x2),ENum(1),Sta),EVar(x3))))")
    testEval(ERun(e2App), "VNum(2)")
