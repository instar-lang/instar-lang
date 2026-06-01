package instar.twocpsopt

import instar.syntax.*
import Stage.*
import Expr.*
import Value.*

trait Base extends munit.FunSuite {
  def testEval(e: Expr, str: String, opt: Set[String] = Set()): Unit =
    Opt.disableAll
    Opt.enable(opt.toSeq*)
    val (v, _) = eval(e)
    assertEquals(show(v), str)
}

// -- Section 6: Common sub-expression elimination ------------------------

class Section6_CSE extends Base {

  test("cse-1") {
    val e5 = EBinOp2("+",
      EBinOp2("*", ENum2(2), ENum2(3)),
      EBinOp2("*", ENum2(2), ENum2(3)))
    testEval(e5,
      """⟨code:
        |  let x0 = (2 * 3) in
        |  let x1 = (x0 + x0) in
        |  x1⟩""".stripMargin, Set("cse"))
  }

  test("cse-2") {
    val e1 = EBinOp2("+",
      EBinOp2("*", ENum2(2), ENum2(3)),
      EBinOp2("*", ENum2(2), ENum2(3)))
    val e2 = EBinOp2("/", e1, e1)
    testEval(e2,
      """⟨code:
        |  let x0 = (2 * 3) in
        |  let x1 = (x0 + x0) in
        |  let x2 = (x1 / x1) in
        |  x2⟩""".stripMargin, Set("cse"))
  }

  test("cse-lam-1") {
    val f = ELift(ELam("y",
      ELet("z1", EBinOp2("*", ENum2(2), ENum2(3)),
      ELet("z2", EBinOp2("*", ENum2(2), ENum2(3)),
      EBinOp2("+", EVar("y"), EVar("z2"))))))
    val e =
      ELet("f", f,
      ELet("x1", EBinOp2("*", ENum2(2), ENum2(3)),
      EApp2(EVar("f"), ENum2(3))))
    testEval(e,
      """⟨code:
        |  let x3 = λ x0.
        |    let x1 = (2 * 3) in
        |    let x2 = (x0 + x1) in
        |    x2 in
        |  let x4 = (2 * 3) in
        |  let x5 = (x3 3) in
        |  x5⟩""".stripMargin, Set("cse"))
  }

  test("cse-lam-2") {
    val f = ELift(ELam("y",
      ELet("z1", EBinOp2("*", ENum2(2), ENum2(3)),
      ELet("z2", EBinOp2("*", ENum2(2), ENum2(3)),
      EBinOp2("+", EVar("y"), EVar("z2"))))))
    val e =
      ELet("x1", EBinOp2("*", ENum2(2), ENum2(3)),
      ELet("f", f,
      EApp2(EVar("f"), ENum2(3))))
    testEval(e,
      """⟨code:
        |  let x0 = (2 * 3) in
        |  let x3 = λ x1.
        |    let x2 = (x1 + x0) in
        |    x2 in
        |  let x4 = (x3 3) in
        |  x4⟩""".stripMargin, Set("cse"))
  }

  test("cse-cond-1") {
    val e = ECond2(
      EBinOp2("==", ENum2(1), ENum2(2)),
      EBinOp2("*", ENum2(2), ENum2(3)),
      EBinOp2("*", ENum2(2), ENum2(3)),
    )
    testEval(e,
      """⟨code:
        |  let x0 = (1 == 2) in
        |  let x3 = if x0
        |  then
        |    let x1 = (2 * 3) in
        |    x1
        |  else
        |    let x2 = (2 * 3) in
        |    x2 in
        |  x3⟩""".stripMargin, Set("cse"))
  }

  test("cse-cond-2") {
    val e =
      ELet("x0", EBinOp2("*", ENum2(2), ENum2(3)),
      ECond2(
        EBinOp2("==", ENum2(1), ENum2(2)),
        EBinOp2("*", ENum2(2), ENum2(3)),
        EBinOp2("*", ENum2(2), ENum2(3)),
    ))
    testEval(e,
      """⟨code:
        |  let x0 = (2 * 3) in
        |  let x1 = (1 == 2) in
        |  let x2 = if x1
        |  then
        |    x0
        |  else
        |    x0 in
        |  x2⟩""".stripMargin, Set("cse"))
  }
}

// -- Section 7: Constant folding ------------------------------------------

class Section7_Folding extends Base {

  test("folding-1") {
    val e1 = ELet("x", EBinOp2("+", ENum2(1), ENum2(2)),
      ELet("y", EBinOp2("+", ENum2(1), ENum2(2)),
      EBinOp2("*", EVar("x"), EVar("y"))))
    testEval(e1,
      """⟨code:
        |  9⟩""".stripMargin, Set("rewriting"))
  }

  test("folding-2") {
    val e1 = ELift(ELam("z",
      ELet("x", EBinOp2("+", EVar("z"), ENum2(2)),
      ELet("y", EBinOp2("+", ENum2(1), ENum2(2)),
      EBinOp2("*", EVar("x"), EVar("y"))))))
    testEval(e1,
      """⟨code:
        |  let x3 = λ x0.
        |    let x1 = (x0 + 2) in
        |    let x2 = (x1 * 3) in
        |    x2 in
        |  x3⟩""".stripMargin, Set("rewriting"))
  }
}

// -- Section 8: Dead-code elimination -------------------------------------

class Section8_DCE extends Base {

  test("dce") {
    val e2 = ELift(ELam("y",
      ELet("z", EBinOp2("+", EVar("y"), ENum2(2)),
      EVar("y"))))
    testEval(e2,
      """⟨code:
        |  let x2 = λ x0.
        |    x0 in
        |  x2⟩""".stripMargin, Set("dce"))
  }
}

// -- Section 9: Partially-static data -------------------------------------

class Section9_PSD extends Base {

  test("psd-1") {
    val e1 = ELift(ELam("x", EBinOp2("+", ENum2(3), EBinOp2("+", ENum2(1), EVar("x")))))
    testEval(e1,
      """⟨code:
        |  let x3 = λ x0.
        |    let x1 = (1 + x0) in
        |    let x2 = (4 + x0) in
        |    x2 in
        |  x3⟩""".stripMargin, Set("ps"))
  }

  test("psd-2") {
    val e2 = ELift(ELam("x",
      EBinOp2("+", ENum2(1),
      EBinOp2("+", ENum2(1),
      EBinOp2("+", ENum2(1),
      EBinOp2("+", ENum2(1),
      EBinOp2("+", ENum2(1), EVar("x"))))))))
    testEval(e2,
      """⟨code:
        |  let x6 = λ x0.
        |    let x1 = (1 + x0) in
        |    let x2 = (2 + x0) in
        |    let x3 = (3 + x0) in
        |    let x4 = (4 + x0) in
        |    let x5 = (5 + x0) in
        |    x5 in
        |  x6⟩""".stripMargin, Set("ps"))
  }

  test("psd-3") {
    val e3 = ELift(ELam("x",
      ELift(ELam("f",
      EBinOp2("+", ENum2(1),
      EBinOp2("+", ENum2(1),
      EBinOp2("+", ENum2(1),
      EBinOp2("+", ENum2(1),
      EBinOp2("+", ENum2(1), EApp2(EVar("f"), EVar("x")))))))))))
    testEval(e3,
      """⟨code:
        |  let x9 = λ x0.
        |    let x8 = λ x1.
        |      let x2 = (x1 x0) in
        |      let x3 = (1 + x2) in
        |      let x4 = (2 + x2) in
        |      let x5 = (3 + x2) in
        |      let x6 = (4 + x2) in
        |      let x7 = (5 + x2) in
        |      x7 in
        |    x8 in
        |  x9⟩""".stripMargin, Set("ps"))
  }

  test("psd-dce-1") {
    val e1 = ELift(ELam("x", EBinOp2("+", ENum2(3), EBinOp2("+", ENum2(1), EVar("x")))))
    testEval(e1,
      """⟨code:
        |  let x3 = λ x0.
        |    let x2 = (4 + x0) in
        |    x2 in
        |  x3⟩""".stripMargin, Set("ps", "dce"))
  }

  test("psd-dce-2") {
    val e1_5 = ELift(ELam("x",
      ELift(ELam("f",
      ELet("y", EBinOp2("+", ENum2(1), EVar("x")),
      ELet("z", EBinOp2("+", EVar("x"), ENum2(1)),
      EBinOp2("+",
        EApp2(EVar("f"), EVar("y")),
        EApp2(EVar("f"), EVar("z")))))))))
    testEval(e1_5,
      """⟨code:
        |  let x7 = λ x0.
        |    let x6 = λ x1.
        |      let x2 = (1 + x0) in
        |      let x3 = (x1 x2) in
        |      let x4 = (x1 x2) in
        |      let x5 = (x3 + x4) in
        |      x5 in
        |    x6 in
        |  x7⟩""".stripMargin, Set("ps", "dce", "cse"))
  }

  test("psd-dce-3") {
    val e2 = ELift(ELam("x",
      EBinOp2("+", ENum2(1),
      EBinOp2("+", ENum2(1),
      EBinOp2("+", ENum2(1),
      EBinOp2("+", ENum2(1),
      EBinOp2("+", ENum2(1), EVar("x"))))))))
    testEval(e2,
      """⟨code:
        |  let x6 = λ x0.
        |    let x5 = (5 + x0) in
        |    x5 in
        |  x6⟩""".stripMargin, Set("ps", "dce"))
  }

  test("psd-dce-4") {
    val e3 = ELift(ELam("x",
      ELift(ELam("f",
      EBinOp2("+", ENum2(1),
      EBinOp2("+", ENum2(1),
      EBinOp2("+", ENum2(1),
      EBinOp2("+", ENum2(1),
      EBinOp2("+", ENum2(1), EApp2(EVar("f"), EVar("x")))))))))))
    testEval(e3,
      """⟨code:
        |  let x9 = λ x0.
        |    let x8 = λ x1.
        |      let x2 = (x1 x0) in
        |      let x7 = (5 + x2) in
        |      x7 in
        |    x8 in
        |  x9⟩""".stripMargin, Set("ps", "dce"))
  }

  test("psd-dce-5") {
    val e4 = ELift(ELam("x",
      ELift(ELam("y",
      EBinOp2("+",
        EBinOp2("+", ENum2(1), EVar("x")),
        EBinOp2("+", ENum2(1), EVar("y")))))))
    testEval(e4,
      """⟨code:
        |  let x7 = λ x0.
        |    let x6 = λ x1.
        |      let x4 = (2 + x0) in
        |      let x5 = (x4 + x1) in
        |      x5 in
        |    x6 in
        |  x7⟩""".stripMargin, Set("ps", "dce"))
  }

  test("psd-dce-6") {
    val e5 = ELift(ELam("f",
      ELift(ELam("x",
      ELift(ELam("y",
      EBinOp2("+",
        EBinOp2("+", ENum2(1), EApp2(EVar("f"), EVar("x"))),
        EBinOp2("+", ENum2(1), EBinOp2("+", ENum2(1), EApp2(EVar("f"), EVar("y")))))))))))
    testEval(e5,
      """⟨code:
        |  let x12 = λ x0.
        |    let x11 = λ x1.
        |      let x10 = λ x2.
        |        let x3 = (x0 x1) in
        |        let x5 = (x0 x2) in
        |        let x8 = (3 + x3) in
        |        let x9 = (x8 + x5) in
        |        x9 in
        |      x10 in
        |    x11 in
        |  x12⟩""".stripMargin, Set("ps", "dce"))
  }

  test("psd-dce-7") {
    val e6 = ELift(ELam("x",
      ELet("y",
        EBinOp2("+",
          EBinOp2("+", EVar("x"), EVar("x")),
          EVar("x")),
      ELift(ELam("z",
      EBinOp2("+",
        EBinOp2("+", EVar("y"), ENum2(2)),
        EBinOp2("+", EVar("y"), ENum2(1))))))))
    testEval(e6,
      """⟨code:
        |  let x11 = λ x0.
        |    let x10 = λ x3.
        |      let x8 = (6 * x0) in
        |      let x9 = (3 + x8) in
        |      x9 in
        |    x10 in
        |  x11⟩""".stripMargin, Set("ps", "dce"))
  }

  test("psd-dce-8") {
    val e7 = ELift(ELam("x",
      ELet("y", EBinOp2("+", EVar("x"), EVar("x")),
      ELet("f",
        ELift(ELam("z",
        ELift(ELam("w",
        EBinOp2("+",
          EBinOp2("+", EVar("y"), ENum2(1)),
          EBinOp2("+", EVar("y"), ENum2(1))))))),
      EApp2(EVar("f"), EVar("y"))))))
    testEval(e7,
      """⟨code:
        |  let x13 = λ x0.
        |    let x1 = (2 * x0) in
        |    let x11 = λ x2.
        |      let x10 = λ x3.
        |        let x8 = (4 * x0) in
        |        let x9 = (2 + x8) in
        |        x9 in
        |      x10 in
        |    let x12 = (x11 x1) in
        |    x12 in
        |  x13⟩""".stripMargin, Set("ps", "dce"))
  }

  test("psd-dce-9") {
    val e8 = ELift(ELam("x",
      EBinOp2("*",
        EBinOp2("+", EVar("x"), ENum2(1)),
        EBinOp2("+", EVar("x"), ENum2(1)))))
    testEval(e8,
      """⟨code:
        |  let x7 = λ x0.
        |    let x3 = (2 * x0) in
        |    let x4 = (1 + x3) in
        |    let x5 = (x0 * x0) in
        |    let x6 = (x4 + x5) in
        |    x6 in
        |  x7⟩""".stripMargin, Set("ps", "dce"))
  }
}

// -- Section 10: Inlining with renormalization ----------------------------

class Section10_Inlining extends Base {

  test("inline-1") {
    val f = ELift(ELam("y", EBinOp2("+", EVar("y"), ENum2(2))))
    val arg = ENum2(3)
    val e4 = EApp2(f, arg)
    testEval(e4,
      """⟨code:
        |  let x2 = λ x0.
        |    let x1 = (x0 + 2) in
        |    x1 in
        |  let x3 = (3 + 2) in
        |  x3⟩""".stripMargin, Set("fun-inline"))
  }

  test("inline-2") {
    val f = ELift(ELam("y", EBinOp2("+", EVar("y"), ENum2(2))))
    val arg = ENum2(3)
    val e4 = EApp2(f, arg)
    testEval(e4,
      """⟨code:
        |  let x3 = (3 + 2) in
        |  x3⟩""".stripMargin, Set("fun-inline", "dce"))
  }

  test("inline-3") {
    val e = ELift(ELam("z", EApp2(EVar("z"), ENum2(3))))
    testEval(e,
      """⟨code:
        |  let x2 = λ x0.
        |    let x1 = (x0 3) in
        |    x1 in
        |  x2⟩""".stripMargin, Set("fun-inline"))
  }

  test("inline-4") {
    val e =
      ELet("a", EBinOp2("+", ENum2(42), ENum2(42)),
      ELift(ELam("z",
        ELet("f",
          ELift(ELam("z",
          ELet("x", EBinOp2("+", EVar("z"), EVar("a")),
          ELet("y", EBinOp2("+", ENum2(1), ENum2(2)),
          EBinOp2("*", EVar("x"), EVar("y")))))),
        EApp2(EVar("f"), EVar("z"))))))
    testEval(e,
      """⟨code:
        |  let x0 = (42 + 42) in
        |  let x10 = λ x1.
        |    let x6 = λ x2.
        |      let x3 = (x2 + x0) in
        |      let x4 = (1 + 2) in
        |      let x5 = (x3 * x4) in
        |      x5 in
        |    let x7 = (x1 + x0) in
        |    let x8 = (1 + 2) in
        |    let x9 = (x7 * x8) in
        |    x9 in
        |  x10⟩""".stripMargin, Set("fun-inline"))
  }

  test("inline-nested") {
    val f1 = ELift(ELam("y", EBinOp2("+", EVar("y"), ENum2(2))))
    val f2 = ELift(ELam("z", EApp2(f1, EVar("z"))))
    val arg = ENum2(3)
    val e = EApp2(f2, arg)
    testEval(e,
      """⟨code:
        |  let x6 = (3 + 2) in
        |  x6⟩""".stripMargin, Set("fun-inline", "dce"))
  }

  test("inline-1") {
    val f1 = ELift(ELam("y",
      EBinOp2("+",
        EBinOp2("*", ENum2(42), ENum2(100)),
        EBinOp2("+", EVar("y"), ENum2(2)))))
    val e = ELet("f1", f1,
      ELet("r", EApp2(EVar("f1"), ENum2(3)),
      ELet("a", EBinOp2("*", ENum2(42), ENum2(100)),
      EBinOp2("/", EVar("r"), EVar("a")))))
    testEval(e,
      """⟨code:
        |  let x4 = λ x0.
        |    let x1 = (42 * 100) in
        |    let x2 = (x0 + 2) in
        |    let x3 = (x1 + x2) in
        |    x3 in
        |  let x5 = (x4 3) in
        |  let x6 = (42 * 100) in
        |  let x7 = (x5 / x6) in
        |  x7⟩""".stripMargin)
  }

  test("inline-2") {
    val f1 = ELift(ELam("y",
      EBinOp2("+",
        EBinOp2("*", ENum2(42), ENum2(100)),
        EBinOp2("+", EVar("y"), ENum2(2)))))
    val e = ELet("f1", f1,
      ELet("r", EApp2(EVar("f1"), ENum2(3)),
      ELet("a", EBinOp2("*", ENum2(42), ENum2(100)),
      EBinOp2("/", EVar("r"), EVar("a")))))
    testEval(e,
      """⟨code:
        |  let x4 = λ x0.
        |    let x1 = (42 * 100) in
        |    let x2 = (x0 + 2) in
        |    let x3 = (x1 + x2) in
        |    x3 in
        |  let x5 = (42 * 100) in
        |  let x6 = (3 + 2) in
        |  let x7 = (x5 + x6) in
        |  let x8 = (42 * 100) in
        |  let x9 = (x7 / x8) in
        |  x9⟩""".stripMargin, Set("fun-inline"))
  }

  test("inline-cse-3") {
    val f1 = ELift(ELam("y",
      EBinOp2("+",
        EBinOp2("*", ENum2(42), ENum2(100)),
        EBinOp2("+", EVar("y"), ENum2(2)))))
    val e = ELet("f1", f1,
      ELet("r", EApp2(EVar("f1"), ENum2(3)),
      ELet("a", EBinOp2("*", ENum2(42), ENum2(100)),
      EBinOp2("/", EVar("r"), EVar("a")))))
    testEval(e,
      """⟨code:
        |  let x4 = λ x0.
        |    let x1 = (42 * 100) in
        |    let x2 = (x0 + 2) in
        |    let x3 = (x1 + x2) in
        |    x3 in
        |  let x5 = (42 * 100) in
        |  let x6 = (3 + 2) in
        |  let x7 = (x5 + x6) in
        |  let x8 = (x7 / x5) in
        |  x8⟩""".stripMargin, Set("fun-inline", "cse"))
  }

  test("inline-cse-4") {
    val f1 = ELift(ELam("y",
      EBinOp2("+",
        EBinOp2("*", ENum2(42), ENum2(100)),
        EBinOp2("+", EVar("y"), ENum2(2)))))
    val e = ELet("f1", f1,
      ELet("r", EApp2(EVar("f1"), ENum2(3)),
      ELet("a", EBinOp2("*", ENum2(42), ENum2(100)),
      EBinOp2("/", EVar("r"), EVar("a")))))
    testEval(e,
      """⟨code:
        |  let x5 = (42 * 100) in
        |  let x6 = (3 + 2) in
        |  let x7 = (x5 + x6) in
        |  let x8 = (x7 / x5) in
        |  x8⟩""".stripMargin, Set("fun-inline", "cse", "dce"))
  }

  test("inline-cse-5") {
    val f1 = ELift(ELam("y",
      EBinOp2("+",
        EBinOp2("*", ENum2(42), ENum2(100)),
        EBinOp2("+", EVar("y"), ENum2(2)))))
    val e = ELet("f1", f1,
      ELet("r", EApp2(EVar("f1"), ENum2(3)),
      ELet("a", EBinOp2("*", ENum2(42), ENum2(100)),
      EBinOp2("/", EVar("r"), EVar("a")))))
    testEval(e,
      """⟨code:
        |  let x3 = λ x0.
        |    let x1 = (x0 + 2) in
        |    let x2 = (4200 + x1) in
        |    x2 in
        |  1⟩""".stripMargin, Set("fun-inline", "cse", "rewriting"))
  }

  test("inline-cse-6") {
    val f1 = ELift(ELam("y",
      EBinOp2("+",
        EBinOp2("*", ENum2(42), ENum2(100)),
        EBinOp2("+", EVar("y"), ENum2(2)))))
    val e = ELet("f1", f1,
      ELet("r", EApp2(EVar("f1"), ENum2(3)),
      ELet("a", EBinOp2("*", ENum2(42), ENum2(100)),
      EBinOp2("/", EVar("r"), EVar("a")))))
    testEval(e,
      """⟨code:
        |  1⟩""".stripMargin, Set("fun-inline", "cse", "rewriting", "dce"))
  }

  test("cond-simp-1") {
    val e1 = ECond2(
      EBinOp2("==", ENum2(1), ENum2(2)),
      EBinOp2("*", ENum2(3), ENum2(4)),
      EBinOp2("*", ENum2(4), ENum2(5)),
    )
    testEval(e1,
      """⟨code:
        |  20⟩""".stripMargin, Set("rewriting", "simp-cond"))
    val e2 = ECond2(
      EBinOp2("==", ENum2(2), ENum2(2)),
      EBinOp2("*", ENum2(3), ENum2(4)),
      EBinOp2("*", ENum2(4), ENum2(5)),
    )
    testEval(e2,
      """⟨code:
        |  12⟩""".stripMargin, Set("rewriting", "simp-cond"))
  }

  test("cond-simp-2") {
    val e1 = ELift(ELam("y",
      ELet("z1", EBinOp2("*", ENum2(2), ENum2(3)),
      ECond2(
        EBinOp2("==", EVar("z1"), ENum2(6)),
        EBinOp2("*", EVar("y"), ENum2(4)),
        EBinOp2("*", EVar("y"), EBinOp2("+", EVar("y"), ENum2(4)))))))
    testEval(e1,
      """⟨code:
        |  let x5 = λ x0.
        |    let x4 = (x0 * 4) in
        |    x4 in
        |  x5⟩""".stripMargin, Set("rewriting", "simp-cond"))
    val e2 = ELift(ELam("y",
      ELet("z1", EBinOp2("*", ENum2(2), ENum2(3)),
      ECond2(
        EBinOp2("==", EVar("z1"), ENum2(7)),
        EBinOp2("*", EVar("y"), ENum2(4)),
        EBinOp2("*", EVar("y"), EBinOp2("+", EVar("y"), ENum2(4)))))))
    testEval(e2,
      """⟨code:
        |  let x6 = λ x0.
        |    let x4 = (x0 + 4) in
        |    let x5 = (x0 * x4) in
        |    x5 in
        |  x6⟩""".stripMargin, Set("rewriting", "simp-cond"))
  }
}

// -- Section 11: Code motion / lambda-hoisting ----------------------------

class Section11_Hoisting extends Base {

  test("hoist-1") {
    val e = ELift(ELam("z",
      ELet("x", EBinOp2("+", EVar("z"), ENum2(2)),
      ELet("y", EBinOp2("+", ENum2(1), ENum2(2)),
      EBinOp2("*", EVar("x"), EVar("y"))))))
    testEval(e,
      """⟨code:
        |  let x5 = (1 + 2) in
        |  let x6 = λ x0.
        |    let x1 = (x0 + 2) in
        |    let x3 = (x1 * x5) in
        |    x3 in
        |  x6⟩""".stripMargin, Set("lam-hoist"))
  }

  test("hoist-2a") {
    val e =
      ELet("a", EBinOp2("+", ENum2(42), ENum2(42)),
      ELift(ELam("z",
        ELet("x", EBinOp2("+", EVar("z"), ENum2(2)),
        ELet("y", EBinOp2("+", ENum2(1), ENum2(2)),
        EBinOp2("*", EVar("x"), EVar("y")))))))
    testEval(e,
      """⟨code:
        |  let x0 = (42 + 42) in
        |  let x6 = (1 + 2) in
        |  let x7 = λ x1.
        |    let x2 = (x1 + 2) in
        |    let x4 = (x2 * x6) in
        |    x4 in
        |  x7⟩""".stripMargin, Set("lam-hoist"))
  }

  test("hoist-2b") {
    val e =
      ELet("a", EBinOp2("+", ENum2(42), ENum2(42)),
      ELift(ELam("z",
        ELet("x", EBinOp2("+", EVar("z"), ENum2(2)),
        ELet("y", EBinOp2("+", EVar("a"), ENum2(2)),
        EBinOp2("*", EVar("x"), EVar("y")))))))
    testEval(e,
      """⟨code:
        |  let x0 = (42 + 42) in
        |  let x6 = (x0 + 2) in
        |  let x7 = λ x1.
        |    let x2 = (x1 + 2) in
        |    let x4 = (x2 * x6) in
        |    x4 in
        |  x7⟩""".stripMargin, Set("lam-hoist"))
  }

  test("hoist-nested") {
    val e =
      ELet("a", EBinOp2("+", ENum2(42), ENum2(42)),
      ELift(ELam("w",
        ELet("f",
          ELift(ELam("z",
          ELet("x", EBinOp2("+", EVar("z"), EVar("a")),
          ELet("y", EBinOp2("+", ENum2(1), ENum2(2)),
          EBinOp2("*", EVar("x"), EVar("y")))))),
        EApp2(EVar("f"), EVar("w"))))))
    testEval(e,
      """⟨code:
        |  let x0 = (42 + 42) in
        |  let x11 = (1 + 2) in
        |  let x12 = λ x1.
        |    let x8 = λ x2.
        |      let x3 = (x2 + x0) in
        |      let x5 = (x3 * x11) in
        |      x5 in
        |    let x9 = (x8 x1) in
        |    x9 in
        |  x12⟩""".stripMargin, Set("lam-hoist"))
  }
}

// -- Section 12: Extensions -----------------------------------------------

// --- Call-by-name ---

class Section12_CBN extends Base {

  test("cbn") {
    val e1 = ECBNApp(ELam("x", EBinOp("+", EVar("x"), EVar("x"), Dyn)),
             EBinOp2("*", ENum2(21), ENum2(2)))
    testEval(e1,
      """⟨code:
        |  let x0 = (21 * 2) in
        |  let x1 = (21 * 2) in
        |  let x2 = (x0 + x1) in
        |  x2⟩""".stripMargin)
    val e2 = EApp1(ELam("x", EBinOp("+", EVar("x"), EVar("x"), Dyn)),
             EBinOp2("*", ENum2(21), ENum2(2)))
    testEval(e2,
      """⟨code:
        |  let x0 = (21 * 2) in
        |  let x1 = (x0 + x0) in
        |  x1⟩""".stripMargin)
  }

  test("cbn-lam") {
    val e1 = EApp(EBNLam("x", EBinOp("+", EVar("x"), EVar("x"), Dyn)),
             EBinOp2("*", ENum2(21), ENum2(2)), Sta)
    testEval(e1,
      """⟨code:
        |  let x0 = (21 * 2) in
        |  let x1 = (21 * 2) in
        |  let x2 = (x0 + x1) in
        |  x2⟩""".stripMargin)
    val e2 = EApp1(ELam("x", EBinOp("+", EVar("x"), EVar("x"), Dyn)),
             EBinOp2("*", ENum2(21), ENum2(2)))
    testEval(e2,
      """⟨code:
        |  let x0 = (21 * 2) in
        |  let x1 = (x0 + x0) in
        |  x1⟩""".stripMargin)
  }
}

// --- Intensional analysis ---

class Section12_Analysis extends Base {

  test("is-app-1") {
    val e =
      ELet("app", EApp2(ELift(ELam("x", EVar("x"))), ENum2(42)),
      ECond1(EIsApp(EVar("app")), EBool2(true), EBool2(false)))
    testEval(e,
      """⟨code:
        |  let x1 = λ x0.
        |    x0 in
        |  let x2 = (x1 42) in
        |  true⟩""".stripMargin)
  }

  test("is-app-2") {
    val e = EIsApp(ENum2(42))
    testEval(e, "false")
  }

  test("is-app-conflict") {
    val e = ELift(EIsApp(EApp2(ELift(ELam("x", EVar("x"))), ENum2(42))))
    testEval(e,
      """⟨code:
        |  let x1 = λ x0.
        |    x0 in
        |  let x2 = (x1 42) in
        |  true⟩""".stripMargin, Set("dce"))
    testEval(e,
      """⟨code:
        |  false⟩""".stripMargin, Set("fun-inline", "dce"))
  }
}

// --- Recursive functions, mutable references, run ---

class Section12_Extensions extends Base {

  val e1 = EApp2(
    ELift(ELam("x", EBinOp2("+", EVar("x"), ENum2(1)))),
    ENum2(41))

  val e2 = ELift(ELam("x", EBinOp2("+", EVar("x"), ENum2(1))))

  val e3 = ELift(ELam("y", EBinOp2("*", EVar("y"), ENum2(42))))

  val e4 = ECond(
    EBool2(true),
    EApp2(e2, ENum2(10)),
    EApp2(e3, ENum2(20)),
    Dyn
  )

  val e6 = ELetRec(
    "fact",
    ELam("n", ECond1(
        EBinOp1("<=", EVar("n"), ENum(1)),
        ENum(1),
        EBinOp1("*",
          EVar("n"),
          EApp1(EVar("fact"), EBinOp1("-", EVar("n"), ENum(1)))),
      )),
    EApp1(EVar("fact"), ENum(5))
  )

  val e7 = ELetRec(
    "power",
    ELam("x", ELam("n", ECond1(
        EBinOp1("==", EVar("n"), ENum(0)),
        ENum(1),
        EBinOp1("*",
          EVar("x"),
          EApp1(EApp1(EVar("power"), EVar("x")), EBinOp1("-", EVar("n"), ENum(1)))),
      ))),
    EApp1(EApp1(EVar("power"), ENum(2)), ENum(10))
  )

  val e11 = {
    val fib = EFix("fib", ELift(ELam("n",
      ECond2(
        EBinOp2("<=", EVar("n"), ENum2(1)),
        ENum2(1),
        EBinOp2("*",
          EVar("n"),
          EApp2(EVar("fib"), EBinOp2("-", EVar("n"), ENum2(1)))),
      ))), Dyn)
    ELet("fib", fib, EApp2(EVar("fib"), ENum2(5)))
  }

  test("lam-app") {
    testEval(e1,
      """⟨code:
        |  let x2 = λ x0.
        |    let x1 = (x0 + 1) in
        |    x1 in
        |  let x3 = (x2 41) in
        |  x3⟩""".stripMargin)
    testEval(e2,
      """⟨code:
        |  let x2 = λ x0.
        |    let x1 = (x0 + 1) in
        |    x1 in
        |  x2⟩""".stripMargin)
  }

  test("cond") {
    testEval(e4,
      """⟨code:
        |  let x8 = if true
        |  then
        |    let x2 = λ x0.
        |      let x1 = (x0 + 1) in
        |      x1 in
        |    let x3 = (x2 10) in
        |    x3
        |  else
        |    let x6 = λ x4.
        |      let x5 = (x4 * 42) in
        |      x5 in
        |    let x7 = (x6 20) in
        |    x7 in
        |  x8⟩""".stripMargin)
  }

  test("rec") {
    testEval(e6, "120")
    testEval(e7, "1024")
  }

  val e10 = {
    val fib = EFix("fib", ELam("n",
      ECond1(
        EBinOp1("<=", EVar("n"), ENum(1)),
        ENum(1),
        EBinOp1("*",
          EVar("n"),
          EApp1(EVar("fib"), EBinOp1("-", EVar("n"), ENum(1))))
      )), Sta)
    ELet("fib", fib, EApp1(EVar("fib"), ENum(5)))
  }

  test("stuck") {
    intercept[RuntimeException] {
      val e = ELet("x", EAlloc2(ENum2(0)), ENum(10))
      eval(e)
    }
  }

  test("fix") {
    testEval(e10, "120")
  }

  test("fix-second-stage") {
    testEval(e11,
      """⟨code:
        |  let x8 = fix f0.
        |    let x7 = λ x1.
        |      let x2 = (x1 <= 1) in
        |      let x6 = if x2
        |      then
        |        1
        |      else
        |        let x3 = (x1 - 1) in
        |        let x4 = (f0 x3) in
        |        let x5 = (x1 * x4) in
        |        x5 in
        |      x6 in
        |    x7 in
        |  let x9 = (x8 5) in
        |  x9⟩""".stripMargin)
    val (VCode(e), _) = eval(e11)
    testEval(e, "120")
  }

  test("lift-loc") {
    val e = ELift(EAlloc1(ENum(42)))
    testEval(e,
      """⟨code:
        |  let x0 = <loc: 0> in
        |  x0⟩""".stripMargin)
  }

  test("lift-curry-lam") {
    val e = ELift(ELam("x", ELift(ELam("y", EBinOp2("+", EVar("x"), EVar("y"))))))
    testEval(e,
      """⟨code:
        |  let x4 = λ x0.
        |    let x3 = λ x1.
        |      let x2 = (x0 + x1) in
        |      x2 in
        |    x3 in
        |  x4⟩""".stripMargin)
  }

  test("run") {
    testEval(ENum(1), "1")
    testEval(ERun(ENum2(1)), "1")
    val e1 =
      ELift(ELam("x", EBinOp2("+", EVar("x"), ENum2(1))))
    testEval(e1,
      """⟨code:
        |  let x2 = λ x0.
        |    let x1 = (x0 + 1) in
        |    x1 in
        |  x2⟩""".stripMargin)
    testEval(ERun(e1),
      """⟨closure: λ x0.
        |  let x1 = (x0 + 1) in
        |  x1⟩""".stripMargin)
    val e2 = ELet(
      "y",
      ELift(ELam("x", EBinOp2("+", EVar("x"), ENum2(1)))),
      EApp2(EVar("y"), ENum2(1)))
    testEval(e2,
      """⟨code:
        |  let x2 = λ x0.
        |    let x1 = (x0 + 1) in
        |    x1 in
        |  let x3 = (x2 1) in
        |  x3⟩""".stripMargin)
    testEval(ERun(e2), "2")
    val e3 = EDeref1(ERun(ELift(EAlloc1(ENum(1)))))
    testEval(e3, "1")
  }
}
