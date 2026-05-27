package instar.experiment.cekm

import instar.experiment.*

class CEKMTest extends munit.FunSuite:
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

  val e4 = ECond2(
    ELift(EBool(true)),
    EApp2(e2, ELift(ENum(10))),
    EApp2(e3, ELift(ENum(20)))
  )

  def testEval(e: Expr, expected: String): Unit =
    assertEquals(show(eval(e)), expected)

  test("lam-app"):
    testEval(e1,
      """⟨code:
        |  let x2 = λx0.
        |    let x1 = (x0 + 1) in
        |    x1 in
        |  let x3 = (x2 41) in
        |  x3⟩""".stripMargin)
    testEval(e2,
      """⟨code:
        |  let x2 = λx0.
        |    let x1 = (x0 + 1) in
        |    x1 in
        |  x2⟩""".stripMargin)

  test("cond"):
    testEval(e4,
      """⟨code:
        |  let x8 = if true
        |  then
        |    let x2 = λx0.
        |      let x1 = (x0 + 1) in
        |      x1 in
        |    let x3 = (x2 10) in
        |    x3
        |  else
        |    let x6 = λx4.
        |      let x5 = (x4 * 42) in
        |      x5 in
        |    let x7 = (x6 20) in
        |    x7 in
        |  x8⟩""".stripMargin)

  test("run"):
    testEval(ENum(1), "1")
    testEval(ERun(ELift(ENum(1))), "1")

    testEval(e2,
      """⟨code:
        |  let x2 = λx0.
        |    let x1 = (x0 + 1) in
        |    x1 in
        |  x2⟩""".stripMargin)
    testEval(ERun(e2),
      """⟨closure: λx0.
        |  let x1 = (x0 + 1) in
        |  x1⟩""".stripMargin)

    val e2App = ELet("y", e2, EApp2(EVar("y"), ELift(ENum(1))))
    testEval(e2App,
      """⟨code:
        |  let x2 = λx0.
        |    let x1 = (x0 + 1) in
        |    x1 in
        |  let x3 = (x2 1) in
        |  x3⟩""".stripMargin)
    testEval(ERun(e2App), "2")
