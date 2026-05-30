package instar.twocps

import instar.*

class TwoCPSTest extends munit.FunSuite:
  import Stage.*
  import Expr.*
  import Value.*

  val e1 = EApp2(
    ELift(ELam("x", EBinOp2("+", EVar("x"), ENum2(1)))),
    ENum2(41)
  )

  val e2 = ELift(
    ELam("x", EBinOp2("+", EVar("x"), ENum2(1)))
  )

  val e3 = ELift(
    ELam("y", EBinOp2("*", EVar("y"), ENum2(42)))
  )

  val e4 = ECond2(
    EBool2(true),
    EApp2(e2, ENum2(10)),
    EApp2(e3, ENum2(20))
  )

  def testEval(e: Expr, expected: String): Unit =
    assertEquals(show(eval(e)), expected)

  test("lam-app"):
    testEval(e1,
      """⟨code:
        |  let x3 = λx0.
        |    let x1 = 1 in
        |    let x2 = (x0 + x1) in
        |    x2 in
        |  let x4 = 41 in
        |  let x5 = (x3 x4) in
        |  x5⟩""".stripMargin)
    testEval(e2,
      """⟨code:
        |  let x3 = λx0.
        |    let x1 = 1 in
        |    let x2 = (x0 + x1) in
        |    x2 in
        |  x3⟩""".stripMargin)

  test("cond"):
    testEval(e4,
      """⟨code:
        |  let x0 = true in
        |  let x13 = if x0
        |  then
        |    let x4 = λx1.
        |      let x2 = 1 in
        |      let x3 = (x1 + x2) in
        |      x3 in
        |    let x5 = 10 in
        |    let x6 = (x4 x5) in
        |    x6
        |  else
        |    let x10 = λx7.
        |      let x8 = 42 in
        |      let x9 = (x7 * x8) in
        |      x9 in
        |    let x11 = 20 in
        |    let x12 = (x10 x11) in
        |    x12 in
        |  x13⟩""".stripMargin)

  test("run"):
    testEval(ENum(1), "1")
    testEval(ERun(ENum2(1)), "1")

    testEval(e2,
      """⟨code:
        |  let x3 = λx0.
        |    let x1 = 1 in
        |    let x2 = (x0 + x1) in
        |    x2 in
        |  x3⟩""".stripMargin)
    testEval(ERun(e2),
      """⟨closure: λx0.
        |  let x1 = 1 in
        |  let x2 = (x0 + x1) in
        |  x2⟩""".stripMargin)

    val e2App = ELet("y", e2, EApp2(EVar("y"), ENum2(1)))
    testEval(e2App,
      """⟨code:
        |  let x3 = λx0.
        |    let x1 = 1 in
        |    let x2 = (x0 + x1) in
        |    x2 in
        |  let x4 = 1 in
        |  let x5 = (x3 x4) in
        |  x5⟩""".stripMargin)
    testEval(ERun(e2App), "2")