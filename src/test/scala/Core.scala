package spmp.core

import Stage.*
import Expr.*
import Type.*
import Value.*

class CoreTest extends munit.FunSuite {

  val e1 = EApp2(
    ELift2(
      ELam("x", None, EBinOp2("+", EVar("x"), ELift2(ENum(1))), None)
    ),
    ELift2(ENum(41))
  )

  val e2 = ELift2(
    ELam("x", None, EBinOp2("+", EVar("x"), ELift2(ENum(1))), None)
  )

  val e3 = ELift2(
    ELam("y", None, EBinOp2("*", EVar("y"), ELift2(ENum(42))), None)
  )

  val e4 = ECond(
    ELift2(EBool(true)),
    EApp2(e2, ELift2(ENum(10))),
    EApp2(e3, ELift2(ENum(20))),
    Dyn
  )

  def e5(stage: Int) = {
    // (Λs. (λx. x +ˢ 1ˢ)ˢ 5ˢ)[stage]
    val f = ESLam(
      "s",
      EApp(
        ELift(
          ELam(
            "x",
            None,
            EBinOp("+", EVar("x"), ELift(ENum(1), SVar("s")), SVar("s")),
            None
          ),
          SVar("s")
        ),
        ELift(ENum(5), SVar("s")),
        SVar("s")
      )
    )
    val arg = SNum(stage)
    ESApp(f, arg)
  }

  def testEval(e: Expr, str: String): Unit =
    val v = eval(e)
    assertEquals(v.toString, str)

  test("lam-app") {
    testEval(
      e1,
      "VCode(ELet(x2,ELam(x0,None,ELet(x1,EBinOp(+,EVar(x0),ENum(1),SNum(0)),EVar(x1)),None),ELet(x3,EApp(EVar(x2),ENum(41),SNum(0)),EVar(x3))))"
    )

    testEval(
      e2,
      "VCode(ELet(x2,ELam(x0,None,ELet(x1,EBinOp(+,EVar(x0),ENum(1),SNum(0)),EVar(x1)),None),EVar(x2)))"
    )
  }

  test("cond") {
    testEval(
      e4,
      "VCode(ELet(x8,ECond(EBool(true),ELet(x2,ELam(x0,None,ELet(x1,EBinOp(+,EVar(x0),ENum(1),SNum(0)),EVar(x1)),None),ELet(x3,EApp(EVar(x2),ENum(10),SNum(0)),EVar(x3))),ELet(x6,ELam(x4,None,ELet(x5,EBinOp(*,EVar(x4),ENum(42),SNum(0)),EVar(x5)),None),ELet(x7,EApp(EVar(x6),ENum(20),SNum(0)),EVar(x7))),SNum(0)),EVar(x8)))"
    )
  }

  test("stage-poly") {
    testEval(e5(0), "VNum(6)")

    testEval(
      e5(1),
      "VCode(ELet(x2,ELam(x0,None,ELet(x1,EBinOp(+,EVar(x0),ENum(1),SNum(0)),EVar(x1)),None),ELet(x3,EApp(EVar(x2),ENum(5),SNum(0)),EVar(x3))))"
    )

    val VCode(e) = eval(e5(1))
    testEval(e, "VNum(6)")
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

    intercept[NoSuchElementException] {
      // run (lift (λx. x + lift 1))
      eval(ERun(e1))
    }

    val e2 = ELet(
      "y",
      ELift2(ELam("x", None, EBinOp2("+", EVar("x"), ELift2(ENum(1))), None)),
      EApp2(EVar("y"), ELift2(ENum(1)))
    )

    testEval(
      e2,
      "VCode(ELet(x2,ELam(x0,None,ELet(x1,EBinOp(+,EVar(x0),ENum(1),SNum(0)),EVar(x1)),None),ELet(x3,EApp(EVar(x2),ENum(1),SNum(0)),EVar(x3))))"
    )
    intercept[NoSuchElementException] {
      // run (let y = lift (λx. x + lift 1) in y lift 1)
      eval(ERun(e2))
    }
  }
}
