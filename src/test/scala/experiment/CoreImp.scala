package instar.experiment.imp

import Stage.*
import Expr.*
import Type.*
import Value.*

class CoreImpTest extends munit.FunSuite {
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

  def testEval(e: Expr, str: String): Unit =
    val v = eval(e)
    assertEquals(v.toString, str)

  test("lam-app") {
    // let x3 =
    //   λx0. let x1 = 1 in let x2 = x0 + x1 in x2
    // let x4 = 41
    // let x5 = x3 x4
    // x5
    testEval(e1, "VCode(ELet(x3,ELam(x0,None,ELet(x1,ENum(1),ELet(x2,EBinOp(+,EVar(x0),EVar(x1),SNum(0)),EVar(x2))),None),ELet(x4,ENum(41),ELet(x5,EApp(EVar(x3),EVar(x4),SNum(0)),EVar(x5)))))")

    testEval(e2, "VCode(ELet(x3,ELam(x0,None,ELet(x1,ENum(1),ELet(x2,EBinOp(+,EVar(x0),EVar(x1),SNum(0)),EVar(x2))),None),EVar(x3)))")
  }

  test("cond") {
    testEval(e4, "VCode(ELet(x0,EBool(true),ELet(x13,ECond(EVar(x0),ELet(x4,ELam(x1,None,ELet(x2,ENum(1),ELet(x3,EBinOp(+,EVar(x1),EVar(x2),SNum(0)),EVar(x3))),None),ELet(x5,ENum(10),ELet(x6,EApp(EVar(x4),EVar(x5),SNum(0)),EVar(x6)))),ELet(x10,ELam(x7,None,ELet(x8,ENum(42),ELet(x9,EBinOp(*,EVar(x7),EVar(x8),SNum(0)),EVar(x9))),None),ELet(x11,ENum(20),ELet(x12,EApp(EVar(x10),EVar(x11),SNum(0)),EVar(x12)))),SNum(0)),EVar(x13))))")
  }

  test("stage-poly") {
    // Note: CoreImp does not handle stage polymorphism
    //testEval(e5(0), "VNum(6)")
    //testEval(e5(1), "VCode(ELet(x3,ELam(x0,None,ELet(x1,ENum(1),ELet(x2,EBinOp(+,EVar(x0),EVar(x1),SNum(0)),EVar(x2))),None),ELet(x4,ENum(5),ELet(x5,EApp(EVar(x3),EVar(x4),SNum(0)),EVar(x5)))))")
    //val VCode(e) = eval(e5(1))
    //testEval(e, "VNum(6)")
  }

  test("run") {
    testEval(ENum(1), "VNum(1)")

    testEval(ERun(ELift2(ENum(1))), "VNum(1)")

    val e1 =
      ELift2(ELam("x", None, EBinOp2("+", EVar("x"), ELift2(ENum(1))), None))

    testEval(
      e1,
      "VCode(ELet(x3,ELam(x0,None,ELet(x1,ENum(1),ELet(x2,EBinOp(+,EVar(x0),EVar(x1),SNum(0)),EVar(x2))),None),EVar(x3)))"
    )

    testEval(
      ERun(e1),
      "VClo(x0,None,ELet(x1,ENum(1),ELet(x2,EBinOp(+,EVar(x0),EVar(x1),SNum(0)),EVar(x2))),None,Map())"
    )

    val e2 = ELet(
      "y",
      ELift2(ELam("x", None, EBinOp2("+", EVar("x"), ELift2(ENum(1))), None)),
      EApp2(EVar("y"), ELift2(ENum(1)))
    )

    testEval(
      e2,
      "VCode(ELet(x3,ELam(x0,None,ELet(x1,ENum(1),ELet(x2,EBinOp(+,EVar(x0),EVar(x1),SNum(0)),EVar(x2))),None),ELet(x4,ENum(1),ELet(x5,EApp(EVar(x3),EVar(x4),SNum(0)),EVar(x5)))))"
    )

    testEval(
      ERun(e2),
      "VNum(2)"
    )
  }
}