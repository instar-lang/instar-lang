package instar.interp

import instar.syntax.*
import instar.syntax.given
import Stage.*
import Expr.*
import Type.*
import Value.*

trait Base extends munit.FunSuite {
  def testEval(e: Expr, str: String, opt: Set[String] = Set()): Unit =
    Opt.disableAll
    Opt.enable(opt.toSeq: _*)
    val (v, _) = eval(e)
    assertEquals(v.toString, str)
}

class Playground extends Base {
  test("cbn") {
    val e1 = ECBNApp(ELam("x", None, EBinOp("+", EVar("x"), EVar("x"), Dyn), None),
             EBinOp2("*", ENum2(21), ENum2(2)))
    testEval(e1, """
    VCode(
      ELet(x0,EBinOp(*,ENum(21),ENum(2),Some(SNum(1))),
      ELet(x1,EBinOp(*,ENum(21),ENum(2),Some(SNum(1))),
      ELet(x2,EBinOp(+,EVar(x0),EVar(x1),Some(SNum(1))),EVar(x2)))))
     """.stripMargin.replaceAll("\n", "").replaceAll(" ", ""))

    val e2 = EApp1(ELam("x", None, EBinOp("+", EVar("x"), EVar("x"), Dyn), None),
             EBinOp2("*", ENum2(21), ENum2(2)))
    testEval(e2, "VCode(ELet(x0,EBinOp(*,ENum(21),ENum(2),Some(SNum(1))),ELet(x1,EBinOp(+,EVar(x0),EVar(x0),Some(SNum(1))),EVar(x1))))")
  }

  test("cbn-lam") {
    val e1 = EApp(EBNLam("x", None, EBinOp("+", EVar("x"), EVar("x"), Dyn), None),
             EBinOp2("*", ENum2(21), ENum2(2)), Sta)
    testEval(e1, """
    VCode(
      ELet(x0,EBinOp(*,ENum(21),ENum(2),Some(SNum(1))),
      ELet(x1,EBinOp(*,ENum(21),ENum(2),Some(SNum(1))),
      ELet(x2,EBinOp(+,EVar(x0),EVar(x1),Some(SNum(1))),EVar(x2)))))
     """.stripMargin.replaceAll("\n", "").replaceAll(" ", ""))

    val e2 = EApp1(ELam("x", None, EBinOp("+", EVar("x"), EVar("x"), Dyn), None),
             EBinOp2("*", ENum2(21), ENum2(2)))
    testEval(e2, "VCode(ELet(x0,EBinOp(*,ENum(21),ENum(2),Some(SNum(1))),ELet(x1,EBinOp(+,EVar(x0),EVar(x0),Some(SNum(1))),EVar(x1))))")
  }

}

class LamHoist extends Base {
  test("let-lam-hoist-1") {
    val e =
      ELift2(ELam("z", None,
        ELet("x", EBinOp2("+", EVar("z"), ENum2(2)),
          ELet("y", EBinOp2("+", ENum2(1), ENum2(2)),
            EBinOp2("*", EVar("x"), EVar("y"))
          )),
        None))
    val exp = """
    VCode(
      ELet(x5,EBinOp(+,ENum(1),ENum(2),Some(SNum(1))),
      ELet(x6,ELam(x0,None,
        ELet(x1,EBinOp(+,EVar(x0),ENum(2),Some(SNum(1))),
        ELet(x3,EBinOp(*,EVar(x1),EVar(x5),Some(SNum(1))),
        EVar(x3))),None),
      EVar(x6))))
    """.stripMargin.replaceAll("\n", "").replaceAll(" ", "")
    testEval(e, exp, Set("lam-hoist"))
  }

  test("let-lam-hoist-2") {
    /*
      let a = 42 + 42
      lift(λz. let x = z + 2 in let y = 1 + 2 in x * y)
      =>
      let x0 = 42 + 42
      let x3 = 1 + 2
      let x5 = λx1.
        let x2 = x1 + 2
        let x4 = x2 * x3
        x4
      x5
    */
    val e =
      ELet("a", EBinOp2("+", ENum2(42), ENum2(42)),
      ELift2(ELam("z", None,
        ELet("x", EBinOp2("+", EVar("z"), ENum2(2)),
          ELet("y", EBinOp2("+", ENum2(1), ENum2(2)),
            EBinOp2("*", EVar("x"), EVar("y"))
          )),
        None)))
    val exp = """
    VCode(
      ELet(x0,EBinOp(+,ENum(42),ENum(42),Some(SNum(1))),
      ELet(x6,EBinOp(+,ENum(1),ENum(2),Some(SNum(1))),
      ELet(x7,ELam(x1,None,
        ELet(x2,EBinOp(+,EVar(x1),ENum(2),Some(SNum(1))),
        ELet(x4,EBinOp(*,EVar(x2),EVar(x6),Some(SNum(1))),
        EVar(x4))),None),
      EVar(x7)))))
    """.stripMargin.replaceAll("\n", "").replaceAll(" ", "")
    testEval(e, exp, Set("lam-hoist"))
  }

  test("let-lam-hoist-2") {
    /*
      let a = 42 + 42
      lift(λz. let x = z + 2 in let y = a + 2 in x * y)
      =>
      let x0 = 42 + 42
      let x3 = x0 + 2
      let x5 = λx1.
        let x2 = x1 + 2
        let x4 = x2 * x3
        x4
      x5
    */
    val e =
      ELet("a", EBinOp2("+", ENum2(42), ENum2(42)),
      ELift2(ELam("z", None,
        ELet("x", EBinOp2("+", EVar("z"), ENum2(2)),
          ELet("y", EBinOp2("+", EVar("a"), ENum2(2)),
            EBinOp2("*", EVar("x"), EVar("y"))
          )),
        None)))
    val exp = """
    VCode(
      ELet(x0,EBinOp(+,ENum(42),ENum(42),Some(SNum(1))),
      ELet(x6,EBinOp(+,EVar(x0),ENum(2),Some(SNum(1))),
      ELet(x7,ELam(x1,None,
        ELet(x2,EBinOp(+,EVar(x1),ENum(2),Some(SNum(1))),
        ELet(x4,EBinOp(*,EVar(x2),EVar(x6),Some(SNum(1))),
        EVar(x4))),None),
      EVar(x7)))))
    """.stripMargin.replaceAll("\n", "").replaceAll(" ", "")
    testEval(e, exp, Set("lam-hoist"))
  }

  test("let-lam-hoist-nested") {
    /*
    let a = 42 + 42
    lift { λw.
      let f = λz.
        let x = z + a
        let y = 1 + 2
        x * y
      f(w)
    }
    =>
    let x0 = 42 + 42
    let x11 = 1 + 2
    let x12 = λx1.
      let x8 = λx2.
        let x3 = x2 + x0
        let x5 = x3 * x11
        x5
      let x9 = x1 + x0
      x9
    x12
    }
    */

    val e =
      ELet("a", EBinOp2("+", ENum2(42), ENum2(42)),
      ELift2(ELam("w", None,
        ELet("f", ELift2(ELam("z", None,
          ELet("x", EBinOp2("+", EVar("z"), EVar("a")),
            ELet("y", EBinOp2("+", ENum2(1), ENum2(2)),
              EBinOp2("*", EVar("x"), EVar("y"))
            )),
          None)),
        EApp2(EVar("f"), EVar("w"))), None)))


    val exp = """
    VCode(
      ELet(x0,EBinOp(+,ENum(42),ENum(42),Some(SNum(1))),
      ELet(x11,EBinOp(+,ENum(1),ENum(2),Some(SNum(1))),
      ELet(x12,ELam(x1,None,
        ELet(x8,ELam(x2,None,
          ELet(x3,EBinOp(+,EVar(x2),EVar(x0),Some(SNum(1))),
          ELet(x5,EBinOp(*,EVar(x3),EVar(x11),Some(SNum(1))),
          EVar(x5))),None),
        ELet(x9,EApp(EVar(x8),EVar(x1),Some(SNum(1))),
        EVar(x9))),None),
      EVar(x12)))))
    """.stripMargin.replaceAll("\n", "").replaceAll(" ", "")

    testEval(e, exp, Set("lam-hoist"))
  }
}

class CoreEffOpt extends Base {

  test("opt-rewriting-1") {
    val e1 = ELet("x", EBinOp2("+", ENum2(1), ENum2(2)),
      ELet("y", EBinOp2("+", ENum2(1), ENum2(2)),
        EBinOp2("*", EVar("x"), EVar("y"))
      ))
    testEval(e1, "VCode(ENum(9))", Set("rewriting"))
  }

  test("opt-rewriting-2") {
    val e1 =
      ELift2(ELam("z", None,
        ELet("x", EBinOp2("+", EVar("z"), ENum2(2)),
          ELet("y", EBinOp2("+", ENum2(1), ENum2(2)),
            EBinOp2("*", EVar("x"), EVar("y"))
          )),
        None))
    testEval(e1, "VCode(ELet(x3,ELam(x0,None,ELet(x1,EBinOp(+,EVar(x0),ENum(2),Some(SNum(1))),ELet(x2,EBinOp(*,EVar(x1),ENum(3),Some(SNum(1))),EVar(x2))),None),EVar(x3)))", Set("rewriting"))
  }

  test("opt-dce") {
    val e2 = ELift2(ELam("y", None,
      ELet("z", EBinOp2("+", EVar("y"), ENum2(2)),
        EVar("y")),
      None))

    testEval(e2, "VCode(ELet(x2,ELam(x0,None,EVar(x0),None),EVar(x2)))", Set("dce"))
  }

  test("opt-no-let-lam") {
    val f = ELift2(ELam("y", None,
        EBinOp2("+", EVar("y"), ENum2(2)),
      None))
    val arg = ENum2(3)
    val e3 = EApp2(f, arg)

    // generated code:
    // let x2 = app (lam x0. let x1 = x0 + 2 in x1) 3
    testEval(e3, "VCode(ELet(x2,EApp(ELam(x0,None,ELet(x1,EBinOp(+,EVar(x0),ENum(2),Some(SNum(1))),EVar(x1)),None),ENum(3),Some(SNum(1))),EVar(x2)))", Set("no-let-lam"))
  }

  test("opt-app-inline-1") {
    // In this test case, we enable "no-let-lam" so that lambdas are not let-inserted, so that "fun-inline" will match
    // EApp term whose application term is an ELam directly.

    val f = ELift2(ELam("y", None,
        EBinOp2("+", EVar("y"), ENum2(2)),
      None))
    val arg = ENum2(3)
    val e4 = EApp2(f, arg)

    // Naively inlining the function application would yield:
    // let x2 = { let x1 = 3 + 2 in x1 } in x2
    // which is not ANF anymore, since the right-hand side of x2 is not a value
    // We have performed "renormalization" here to ensure ANF:
    // let x1 = 3 + 2
    // x1
    testEval(e4, "VCode(ELet(x2,EBinOp(+,ENum(3),ENum(2),Some(SNum(1))),EVar(x2)))", Set("fun-inline", "no-let-lam"))
  }

  test("opt-app-inline-2") {
    val f = ELift2(ELam("y", None,
        EBinOp2("+", EVar("y"), ENum2(2)),
      None))
    val arg = ENum2(3)
    val e4 = EApp2(f, arg)

    // Not let-inserting lambdas is okay as well, since "fun-inline" can query the corresponding lambda by its let-bound name.
    // But in this case, we need DCE to remove the unused lambda after inlining.
    testEval(e4, "VCode(ELet(x3,EBinOp(+,ENum(3),ENum(2),Some(SNum(1))),EVar(x3)))", Set("fun-inline", "dce"))
  }

  test("opt-app-inline-3") {
    val e = ELift2(ELam("z", None, EApp2(EVar("z"), ENum2(3)), None))
    testEval(e, "VCode(ELet(x2,ELam(x0,None,ELet(x1,EApp(EVar(x0),ENum(3),Some(SNum(1))),EVar(x1)),None),EVar(x2)))", Set("fun-inline"))
  }

  test("opt-app-inline-4") {
    val e =
      ELet("a", EBinOp2("+", ENum2(42), ENum2(42)),
      ELift2(ELam("z", None,
        ELet("f", ELift2(ELam("z", None,
          ELet("x", EBinOp2("+", EVar("z"), EVar("a")),
            ELet("y", EBinOp2("+", ENum2(1), ENum2(2)),
              EBinOp2("*", EVar("x"), EVar("y"))
            )),
          None)),
        EApp2(EVar("f"), EVar("z"))), None)))
    val exp = """
    VCode(
      ELet(x0,EBinOp(+,ENum(42),ENum(42),Some(SNum(1))),
      ELet(x10,ELam(x1,None,
        ELet(x6,ELam(x2,None,
          ELet(x3,EBinOp(+,EVar(x2),EVar(x0),Some(SNum(1))),
          ELet(x4,EBinOp(+,ENum(1),ENum(2),Some(SNum(1))),
          ELet(x5,EBinOp(*,EVar(x3),EVar(x4),Some(SNum(1))),EVar(x5)))),None),
        ELet(x7,EBinOp(+,EVar(x1),EVar(x0),Some(SNum(1))),
        ELet(x8,EBinOp(+,ENum(1),ENum(2),Some(SNum(1))),
        ELet(x9,EBinOp(*,EVar(x7),EVar(x8),Some(SNum(1))),
        EVar(x9))))),None),
      EVar(x10))))
    """.stripMargin.replaceAll("\n", "").replaceAll(" ", "")
    testEval(e, exp, Set("fun-inline"))
  }

  test("opt-app-inline-nested-1") {
    val f1 = ELift2(ELam("y", None,
        EBinOp2("+", EVar("y"), ENum2(2)),
      None))
    val f2 = ELift2(ELam("z", None,
        EApp2(f1, EVar("z")),
      None))
    val arg = ENum2(3)
    val e = EApp2(f2, arg)
    /*
    (lift(λz. (lift(λy.y+2)) z) 3 => code { let x6 = 3 + 2 in x6 }
    */
    testEval(e, "VCode(ELet(x6,EBinOp(+,ENum(3),ENum(2),Some(SNum(1))),EVar(x6)))" , Set("fun-inline", "dce"))
  }

  test("opt-app-inline-cse") {
    // This test combines function inlining and CSE
    val f1 = ELift2(ELam("y", None,
      EBinOp2("+",
        EBinOp2("*", ENum2(42), ENum2(100)),
        EBinOp2("+", EVar("y"), ENum2(2))),
      None))
    val e = ELet("f1", f1,
      ELet("r", EApp2(EVar("f1"), ENum2(3)),
      ELet("a", EBinOp2("*", ENum2(42), ENum2(100)),
      EBinOp2("/", EVar("r"), EVar("a")))))

    val expNoOpt = """
    |VCode(ELet(x4,
    |  ELam(x0,None,
    |    ELet(x1,EBinOp(*,ENum(42),ENum(100),Some(SNum(1))),
    |    ELet(x2,EBinOp(+,EVar(x0),ENum(2),Some(SNum(1))),
    |    ELet(x3,EBinOp(+,EVar(x1),EVar(x2),Some(SNum(1))),EVar(x3)))),None),
    |ELet(x5,EApp(EVar(x4),ENum(3),Some(SNum(1))),
    |ELet(x6,EBinOp(*,ENum(42),ENum(100),Some(SNum(1))),
    |ELet(x7,EBinOp(/,EVar(x5),EVar(x6),Some(SNum(1))),
    |EVar(x7))))))
    """.stripMargin.replaceAll("\n", "").replaceAll(" ", "")
    testEval(e, expNoOpt)

    val expInline = """
    |VCode(ELet(x4,
    |  ELam(x0,None,
    |  ELet(x1,EBinOp(*,ENum(42),ENum(100),Some(SNum(1))),
    |  ELet(x2,EBinOp(+,EVar(x0),ENum(2),Some(SNum(1))),
    |  ELet(x3,EBinOp(+,EVar(x1),EVar(x2),Some(SNum(1))),EVar(x3)))),None),
    |ELet(x5,EBinOp(*,ENum(42),ENum(100),Some(SNum(1))),
    |ELet(x6,EBinOp(+,ENum(3),ENum(2),Some(SNum(1))),
    |ELet(x7,EBinOp(+,EVar(x5),EVar(x6),Some(SNum(1))),
    |ELet(x8,EBinOp(*,ENum(42),ENum(100),Some(SNum(1))),
    |ELet(x9,EBinOp(/,EVar(x7),EVar(x8),Some(SNum(1))),EVar(x9))))))))
    """.stripMargin.replaceAll("\n", "").replaceAll(" ", "")
    testEval(e, expInline, Set("fun-inline"))

    val expInlineCse = """
    |VCode(ELet(x4,
    |  ELam(x0,None,
    |    ELet(x1,EBinOp(*,ENum(42),ENum(100),Some(SNum(1))),
    |    ELet(x2,EBinOp(+,EVar(x0),ENum(2),Some(SNum(1))),
    |    ELet(x3,EBinOp(+,EVar(x1),EVar(x2),Some(SNum(1))),EVar(x3)))),None),
    |ELet(x5,EBinOp(*,ENum(42),ENum(100),Some(SNum(1))),
    |ELet(x6,EBinOp(+,ENum(3),ENum(2),Some(SNum(1))),
    |ELet(x7,EBinOp(+,EVar(x5),EVar(x6),Some(SNum(1))),
    |ELet(x8,EBinOp(/,EVar(x7),EVar(x5),Some(SNum(1))),EVar(x8)))))))
    """.stripMargin.replaceAll("\n", "").replaceAll(" ", "")
    testEval(e, expInlineCse, Set("fun-inline", "cse"))

    val expInlineCseDce = """
    |VCode(
    |ELet(x5,EBinOp(*,ENum(42),ENum(100),Some(SNum(1))),
    |ELet(x6,EBinOp(+,ENum(3),ENum(2),Some(SNum(1))),
    |ELet(x7,EBinOp(+,EVar(x5),EVar(x6),Some(SNum(1))),
    |ELet(x8,EBinOp(/,EVar(x7),EVar(x5),Some(SNum(1))),EVar(x8))))))
    """.stripMargin.replaceAll("\n", "").replaceAll(" ", "")
    testEval(e, expInlineCseDce, Set("fun-inline", "cse", "dce"))

    val expInlineCseSimp = """
    VCode(ELet(x3,
      ELam(x0,None,ELet(x1,EBinOp(+,EVar(x0),ENum(2),Some(SNum(1))),ELet(x2,EBinOp(+,ENum(4200),EVar(x1),Some(SNum(1))),EVar(x2))),None),
    ENum(1)))
    """.stripMargin.replaceAll("\n", "").replaceAll(" ", "")
    testEval(e, expInlineCseSimp, Set("fun-inline", "cse", "rewriting"))

    val expInlineCseSimpDce = "VCode(ENum(1))"
    testEval(e, expInlineCseSimpDce, Set("fun-inline", "cse", "rewriting", "dce"))
  }

  test("cse-1") {
    val e5 = EBinOp2("+",
      EBinOp2("*", ENum2(2), ENum2(3)),
      EBinOp2("*", ENum2(2), ENum2(3))
    )
    // let x0 = 2 * 3
    // let x1 = x0 + x0
    // x1
    testEval(e5, "VCode(ELet(x0,EBinOp(*,ENum(2),ENum(3),Some(SNum(1))),ELet(x1,EBinOp(+,EVar(x0),EVar(x0),Some(SNum(1))),EVar(x1))))", Set("cse"))
  }

  test("cse-2") {
    val e1 = EBinOp2("+",
      EBinOp2("*", ENum2(2), ENum2(3)),
      EBinOp2("*", ENum2(2), ENum2(3))
    )
    val e2 = EBinOp2("/", e1, e1)

    // let x0 = 2 * 3
    // let x1 = x0 + x0
    // let x2 = x1 / x1
    // x2
    testEval(e2, "VCode(ELet(x0,EBinOp(*,ENum(2),ENum(3),Some(SNum(1))),ELet(x1,EBinOp(+,EVar(x0),EVar(x0),Some(SNum(1))),ELet(x2,EBinOp(/,EVar(x1),EVar(x1),Some(SNum(1))),EVar(x2)))))", Set("cse"))
  }

  test("cse-lam-1") {
    val f = ELift2(ELam("y", None,
        ELet("z1", EBinOp2("*", ENum2(2), ENum2(3)),
        ELet("z2", EBinOp2("*", ENum2(2), ENum2(3)),
          EBinOp2("+", EVar("y"), EVar("z2")))),
      None))
    val e =
      ELet("f", f,
        ELet("x1", EBinOp2("*", ENum2(2), ENum2(3)),
          EApp2(EVar("f"), ENum2(3))))

    // Shouldn't do CSE for x4=2*3 since it's inside a lambda
    // let x3 = lam x0.
    //   let x1 = 2 * 3
    //   let x2 = x0 + x1
    //   x2
    // let x4 = 2 * 3
    // let x5 = x3(3)
    // x5

    testEval(e, "VCode(ELet(x3,ELam(x0,None,ELet(x1,EBinOp(*,ENum(2),ENum(3),Some(SNum(1))),ELet(x2,EBinOp(+,EVar(x0),EVar(x1),Some(SNum(1))),EVar(x2))),None),ELet(x4,EBinOp(*,ENum(2),ENum(3),Some(SNum(1))),ELet(x5,EApp(EVar(x3),ENum(3),Some(SNum(1))),EVar(x5)))))", Set("cse"))
  }

  test("cse-lam-2") {
    val f = ELift2(ELam("y", None,
        ELet("z1", EBinOp2("*", ENum2(2), ENum2(3)),
        ELet("z2", EBinOp2("*", ENum2(2), ENum2(3)),
          EBinOp2("+", EVar("y"), EVar("z2")))),
      None))
    val e =
      ELet("x1", EBinOp2("*", ENum2(2), ENum2(3)),
        ELet("f", f,
          EApp2(EVar("f"), ENum2(3))))

    // Should do CSE:
    // let x0 = 2 * 3
    // let x3 = lam x1.
    //   let x2 = x1 + x0
    //   x2
    // let x4 = x3(3)
    // x4

    testEval(e, "VCode(ELet(x0,EBinOp(*,ENum(2),ENum(3),Some(SNum(1))),ELet(x3,ELam(x1,None,ELet(x2,EBinOp(+,EVar(x1),EVar(x0),Some(SNum(1))),EVar(x2)),None),ELet(x4,EApp(EVar(x3),ENum(3),Some(SNum(1))),EVar(x4)))))", Set("cse"))
  }

  test("cse-cond-1") {
    val e = ECond2(
      EBinOp2("==", ENum2(1), ENum2(2)),
      EBinOp2("*", ENum2(2), ENum2(3)),
      EBinOp2("*", ENum2(2), ENum2(3)),
    )
    // let x0 = 1 == 2
    // let x3 =
    //   if x0 then
    //      let x1 = 2 * 3 in x1
    //   else
    //      let x2 = 2 * 3 in x2
    // x3
    testEval(e, "VCode(ELet(x0,EBinOp(==,ENum(1),ENum(2),Some(SNum(1))),ELet(x3,ECond(EVar(x0),ELet(x1,EBinOp(*,ENum(2),ENum(3),Some(SNum(1))),EVar(x1)),ELet(x2,EBinOp(*,ENum(2),ENum(3),Some(SNum(1))),EVar(x2)),Some(SNum(1))),EVar(x3))))", Set("cse"))
  }

  test("cse-cond-2") {
    val e = ELet("x0", EBinOp2("*", ENum2(2), ENum2(3)),
      ECond2(
        EBinOp2("==", ENum2(1), ENum2(2)),
        EBinOp2("*", ENum2(2), ENum2(3)),
        EBinOp2("*", ENum2(2), ENum2(3)),
    ))
    // let x0 = 2 * 3
    // let x1 = 1 == 2
    // let x2 =
    //   if x1 then x0 else x0
    // x2
    testEval(e, "VCode(ELet(x0,EBinOp(*,ENum(2),ENum(3),Some(SNum(1))),ELet(x1,EBinOp(==,ENum(1),ENum(2),Some(SNum(1))),ELet(x2,ECond(EVar(x1),EVar(x0),EVar(x0),Some(SNum(1))),EVar(x2)))))", Set("cse"))
  }

  test("cond-simp-1") {
    val e1 = ECond2(
      EBinOp2("==", ENum2(1), ENum2(2)),
      EBinOp2("*", ENum2(3), ENum2(4)),
      EBinOp2("*", ENum2(4), ENum2(5)),
    )
    testEval(e1, "VCode(ENum(20))", Set("rewriting", "simp-cond"))

    val e2 = ECond2(
      EBinOp2("==", ENum2(2), ENum2(2)),
      EBinOp2("*", ENum2(3), ENum2(4)),
      EBinOp2("*", ENum2(4), ENum2(5)),
    )
    testEval(e2, "VCode(ENum(12))", Set("rewriting", "simp-cond"))
  }

  test("cond-simp-2") {
    val e1 = ELift2(ELam("y", None,
      ELet("z1", EBinOp2("*", ENum2(2), ENum2(3)),
      ECond2(
        EBinOp2("==", EVar("z1"), ENum2(6)),
        EBinOp2("*", EVar("y"), ENum2(4)),
        EBinOp2("*", EVar("y"), EBinOp2("+", EVar("y"), ENum2(4))))),
    None))

    val exp1 = """
    |VCode(ELet(x5,
    |  ELam(x0,None,
    |    ELet(x4,EBinOp(*,EVar(x0),ENum(4),Some(SNum(1))),
    |    EVar(x4)),None),
    |  EVar(x5)))
    """.stripMargin.replaceAll("\n", "").replaceAll(" ", "")
    testEval(e1, exp1, Set("rewriting", "simp-cond"))

    val e2 = ELift2(ELam("y", None,
      ELet("z1", EBinOp2("*", ENum2(2), ENum2(3)),
      ECond2(
        EBinOp2("==", EVar("z1"), ENum2(7)),
        EBinOp2("*", EVar("y"), ENum2(4)),
        EBinOp2("*", EVar("y"), EBinOp2("+", EVar("y"), ENum2(4))))),
    None))
    val exp2 = """
    |VCode(ELet(x6,
    |  ELam(x0,None,
    |    ELet(x4,EBinOp(+,EVar(x0),ENum(4),Some(SNum(1))),
    |    ELet(x5,EBinOp(*,EVar(x0),EVar(x4),Some(SNum(1))),
    |    EVar(x5))),None),
    |  EVar(x6)))
    """.stripMargin.replaceAll("\n", "").replaceAll(" ", "")
    testEval(e2, exp2, Set("rewriting", "simp-cond"))
  }

  test("rewriting-partial") {
    val e1 = ELift2(ELam("x", None,
      EBinOp2("+", ENum2(3), EBinOp2("+", ENum2(1), EVar("x"))),
      None))
    testEval(e1, "VCode(ELet(x7,ELam(x0,None,ELet(x2,EBinOp(+,ENum(1),EVar(x0),Some(SNum(1))),ELet(x6,EBinOp(+,ENum(4),EVar(x0),Some(SNum(1))),EVar(x6))),None),EVar(x7)))", Set("ps"))

    // λx. 1 + (1 + (1 + (1 + (1 + x))))
    val e2 = ELift2(ELam("x", None,
      EBinOp2("+", ENum2(1), EBinOp2("+",
        ENum2(1), EBinOp2("+",
          ENum2(1), EBinOp2("+",
            ENum2(1), EBinOp2("+",
              ENum2(1), EVar("x")))))),
      None))
    testEval(e2, "VCode(ELet(x19,ELam(x0,None,ELet(x2,EBinOp(+,ENum(1),EVar(x0),Some(SNum(1))),ELet(x6,EBinOp(+,ENum(2),EVar(x0),Some(SNum(1))),ELet(x10,EBinOp(+,ENum(3),EVar(x0),Some(SNum(1))),ELet(x14,EBinOp(+,ENum(4),EVar(x0),Some(SNum(1))),ELet(x18,EBinOp(+,ENum(5),EVar(x0),Some(SNum(1))),EVar(x18)))))),None),EVar(x19)))", Set("ps"))

    // λx. λf. 1 + (1 + (1 + (1 + (1 + f x))))
    val e3 = ELift2(ELam("x", None,
      ELift2(ELam("f", None,
        EBinOp2("+", ENum2(1), EBinOp2("+",
          ENum2(1), EBinOp2("+",
            ENum2(1), EBinOp2("+",
              ENum2(1), EBinOp2("+",
                ENum2(1), EApp2(EVar("f"), EVar("x"))))))),
        None)),
      None))
    testEval(e3, "VCode(ELet(x22,ELam(x0,None,ELet(x21,ELam(x1,None,ELet(x2,EApp(EVar(x1),EVar(x0),Some(SNum(1))),ELet(x4,EBinOp(+,ENum(1),EVar(x2),Some(SNum(1))),ELet(x8,EBinOp(+,ENum(2),EVar(x2),Some(SNum(1))),ELet(x12,EBinOp(+,ENum(3),EVar(x2),Some(SNum(1))),ELet(x16,EBinOp(+,ENum(4),EVar(x2),Some(SNum(1))),ELet(x20,EBinOp(+,ENum(5),EVar(x2),Some(SNum(1))),EVar(x20))))))),None),EVar(x21)),None),EVar(x22)))", Set("ps"))
  }

  test("rewriting-partial-dce") {
    val e1 = ELift2(ELam("x", None,
      EBinOp2("+", ENum2(3), EBinOp2("+", ENum2(1), EVar("x"))),
      None))
    testEval(e1, "VCode(ELet(x7,ELam(x0,None,ELet(x6,EBinOp(+,ENum(4),EVar(x0),Some(SNum(1))),EVar(x6)),None),EVar(x7)))", Set("ps", "dce"))

    // λf. λx. let y = 1 + x in let z = x + 1 in f @[2] y + f @[2] z
    val e1_5 = ELift2(ELam("x", None,
      ELift2(ELam("f", None,
        ELet("y", EBinOp2("+", ENum2(1), EVar("x")),
        ELet("z", EBinOp2("+", EVar("x"), ENum2(1)),
          EBinOp2("+",
            EApp2(EVar("f"), EVar("y")),
            EApp2(EVar("f"), EVar("z"))))),
        None)),
      None))
    testEval(e1_5, "VCode(ELet(x12,ELam(x0,None,ELet(x11,ELam(x1,None,ELet(x3,EBinOp(+,ENum(1),EVar(x0),Some(SNum(1))),ELet(x7,EApp(EVar(x1),EVar(x3),Some(SNum(1))),ELet(x8,EApp(EVar(x1),EVar(x3),Some(SNum(1))),ELet(x10,EBinOp(+,EVar(x7),EVar(x8),Some(SNum(1))),EVar(x10))))),None),EVar(x11)),None),EVar(x12)))", Set("ps", "dce", "cse"))

    // λx. 1 + (1 + (1 + (1 + (1 + x))))
    val e2 = ELift2(ELam("x", None,
      EBinOp2("+", ENum2(1), EBinOp2("+",
        ENum2(1), EBinOp2("+",
          ENum2(1), EBinOp2("+",
            ENum2(1), EBinOp2("+",
              ENum2(1), EVar("x")))))),
      None))
    testEval(e2, "VCode(ELet(x19,ELam(x0,None,ELet(x18,EBinOp(+,ENum(5),EVar(x0),Some(SNum(1))),EVar(x18)),None),EVar(x19)))", Set("ps", "dce"))

    // λx. λf. 1 + (1 + (1 + (1 + (1 + f x))))
    val e3 = ELift2(ELam("x", None,
      ELift2(ELam("f", None,
        EBinOp2("+", ENum2(1), EBinOp2("+",
          ENum2(1), EBinOp2("+",
            ENum2(1), EBinOp2("+",
              ENum2(1), EBinOp2("+",
                ENum2(1), EApp2(EVar("f"), EVar("x"))))))),
        None)),
      None))
    testEval(e3, "VCode(ELet(x22,ELam(x0,None,ELet(x21,ELam(x1,None,ELet(x2,EApp(EVar(x1),EVar(x0),Some(SNum(1))),ELet(x20,EBinOp(+,ENum(5),EVar(x2),Some(SNum(1))),EVar(x20))),None),EVar(x21)),None),EVar(x22)))", Set("ps", "dce"))

    // λx. λy. (1 + x) + (1 + y)
    val e4 = ELift2(ELam("x", None,
      ELift2(ELam("y", None,
        EBinOp2("+",
          EBinOp2("+", ENum2(1), EVar("x")),
          EBinOp2("+", ENum2(1), EVar("y"))),
        None)),
      None))
    testEval(e4, "VCode(ELet(x16,ELam(x0,None,ELet(x15,ELam(x1,None,ELet(x11,EBinOp(+,ENum(2),EVar(x0),Some(SNum(1))),ELet(x14,EBinOp(+,EVar(x11),EVar(x1),Some(SNum(1))),EVar(x14))),None),EVar(x15)),None),EVar(x16)))", Set("ps", "dce"))

    // λf. λx. λy. (1 + f x) + (1 + (1 + f y))
    // the normalization shouldn't change the order of effects
    val e5 = ELift2(ELam("f", None,
      ELift2(ELam("x", None,
        ELift2(ELam("y", None,
          EBinOp2("+",
            EBinOp2("+", ENum2(1), EApp2(EVar("f"), EVar("x"))),
            EBinOp2("+", ENum2(1), EBinOp2("+", ENum2(1), EApp2(EVar("f"), EVar("y"))))),
          None)),
        None)),
      None))
    testEval(e5, "VCode(ELet(x24,ELam(x0,None,ELet(x23,ELam(x1,None,ELet(x22,ELam(x2,None,ELet(x3,EApp(EVar(x0),EVar(x1),Some(SNum(1))),ELet(x6,EApp(EVar(x0),EVar(x2),Some(SNum(1))),ELet(x18,EBinOp(+,ENum(3),EVar(x3),Some(SNum(1))),ELet(x21,EBinOp(+,EVar(x18),EVar(x6),Some(SNum(1))),EVar(x21))))),None),EVar(x22)),None),EVar(x23)),None),EVar(x24)))", Set("ps", "dce"))

    // This is an example that only has add operation, but we can generate a more optimized code by applying ring laws.
    // λx. let y = (x + x) in λz. y + 2 + y + 1
    val e6 = ELift2(ELam("x", None,
      ELet("y",
        EBinOp2("+",
          EBinOp2("+", EVar("x"), EVar("x")),
          EVar("x")),
        ELift2(ELam("z", None,
          EBinOp2("+",
            EBinOp2("+", EVar("y"), ENum2(2)),
            EBinOp2("+", EVar("y"), ENum2(1))),
        None))),
      None))
    testEval(e6, "VCode(ELet(x38,ELam(x0,None,ELet(x37,ELam(x9,None,ELet(x33,EBinOp(*,ENum(6),EVar(x0),Some(SNum(1))),ELet(x36,EBinOp(+,ENum(3),EVar(x33),Some(SNum(1))),EVar(x36))),None),EVar(x37)),None),EVar(x38)))", Set("ps", "dce"))
    // testEval(e6, "VCode(ELet(x14,ELam(x0,None,ELet(x2,EBinOp(+,EVar(x0),EVar(x0),Some(SNum(1))),ELet(x13,ELam(x4,None,ELet(x9,EBinOp(+,EVar(x2),EVar(x2),Some(SNum(1))),ELet(x10,EBinOp(+,EVar(x0),EVar(x0),Some(SNum(1))),ELet(x11,EBinOp(+,EVar(x9),EVar(x10),Some(SNum(1))),ELet(x12,EBinOp(+,ENum(3),EVar(x11),Some(SNum(1))),EVar(x12))))),None),EVar(x13))),None),EVar(x14)))", Set("ps", "dce"))

    // Another example that combines both ring and commutative monoid laws.
    // λx. let y = x + x in let f= λz. λw. y + 1 + y + 1 in f y
    // ~> λ x0 . λ x4 . (2 + (4 * x0))
    val e7 = ELift2(ELam("x", None,
      ELet("y",
        EBinOp2("+",
          EVar("x"),
          EVar("x")),
        ELet("f",
          ELift2(ELam("z", None,
            ELift2(ELam("w", None,
              EBinOp2("+",
                EBinOp2("+", EVar("y"), ENum2(1)),
                EBinOp2("+", EVar("y"), ENum2(1))),
            None)),
          None)),
        EApp2(EVar("f"), EVar("y")))),
      None))
    testEval(e7, "VCode(ELet(x37,ELam(x0,None,ELet(x4,EBinOp(*,ENum(2),EVar(x0),Some(SNum(1))),ELet(x35,ELam(x5,None,ELet(x34,ELam(x6,None,ELet(x30,EBinOp(*,ENum(4),EVar(x0),Some(SNum(1))),ELet(x33,EBinOp(+,ENum(2),EVar(x30),Some(SNum(1))),EVar(x33))),None),EVar(x34)),None),ELet(x36,EApp(EVar(x35),EVar(x4),Some(SNum(1))),EVar(x36)))),None),EVar(x37)))", Set("ps", "dce"))
    // testEval(e7, "VCode(ELet(x15,ELam(x0,None,ELet(x1,EBinOp(+,EVar(x0),EVar(x0),Some(SNum(1))),ELet(x13,ELam(x2,None,ELet(x12,ELam(x3,None,ELet(x8,EBinOp(+,EVar(x0),EVar(x0),Some(SNum(1))),ELet(x9,EBinOp(+,EVar(x8),EVar(x0),Some(SNum(1))),ELet(x10,EBinOp(+,EVar(x9),EVar(x0),Some(SNum(1))),ELet(x11,EBinOp(+,ENum(2),EVar(x10),Some(SNum(1))),EVar(x11))))),None),EVar(x12)),None),ELet(x14,EApp(EVar(x13),EVar(x1),Some(SNum(1))),EVar(x14)))),None),EVar(x15)))", Set("ps", "dce"))


    // λx. (x + 1) * (x + 1)
    // ~> x^2 + 2x + 1
    val e8 = ELift2(ELam("x", None,
      EBinOp2("*",
        EBinOp2("+", EVar("x"), ENum2(1)),
        EBinOp2("+", EVar("x"), ENum2(1))),
      None))
    testEval(e8, "VCode(ELet(x29,ELam(x0,None,ELet(x18,EBinOp(*,ENum(2),EVar(x0),Some(SNum(1))),ELet(x21,EBinOp(+,ENum(1),EVar(x18),Some(SNum(1))),ELet(x23,EBinOp(*,EVar(x0),EVar(x0),Some(SNum(1))),ELet(x28,EBinOp(+,EVar(x21),EVar(x23),Some(SNum(1))),EVar(x28))))),None),EVar(x29)))", Set("ps", "dce"))
  }
}

class CoreEffAnalysis extends Base {
  test("is-app-1") {
    val e =
      ELet("app", EApp2(ELift2(ELam("x", None, EVar("x"), None)), ENum2(42)),
        ECond1(EIsApp(EVar("app")), EBool2(true), EBool2(false)))
    testEval(e, "VCode(ELet(x1,ELam(x0,None,EVar(x0),None),ELet(x2,EApp(EVar(x1),ENum(42),Some(SNum(1))),EBool(true))))")
  }

  test("is-app-2") {
    val e = EIsApp(ENum2(42))
    testEval(e, "VBool(false)")
  }

  test("is-app-conflict") {
    // If we allow intensional code analysis and optimizations at the same time,
    // we may end up incoherent results.
    val e = ELift2(EIsApp(EApp2(ELift2(ELam("x", None, EVar("x"), None)), ENum2(42))))
    testEval(e, "VCode(ELet(x1,ELam(x0,None,EVar(x0),None),ELet(x2,EApp(EVar(x1),ENum(42),Some(SNum(1))),EBool(true))))", Set("dce"))
    testEval(e, "VCode(EBool(false))", Set("fun-inline", "dce"))
  }
}

class CoreEffTest extends Base {

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
    EAscribe(
      ELam("n", Some(TInt), ECond1(
        EBinOp1("<=", EVar("n"), ENum(1)),
        ENum(1),
        EBinOp1("*",
          EVar("n"),
          EApp1(EVar("fact"), EBinOp1("-", EVar("n"), ENum(1)))),
      ), Some(TInt)),
      TFun(TInt, TInt)),
    EApp1(EVar("fact"), ENum(5))
  )

  val e7 = ELetRec(
    "power",
    EAscribe(
      ELam("x", Some(TInt), ELam("n", Some(TInt), ECond1(
        EBinOp1("==", EVar("n"), ENum(0)),
        ENum(1),
        EBinOp1("*",
          EVar("x"),
          EApp1(EApp1(EVar("power"), EVar("x")), EBinOp1("-", EVar("n"), ENum(1)))),
      ), Some(TInt)), Some(TInt)),
      TFun(TInt, TFun(TInt, TInt))),
    EApp1(EApp1(EVar("power"), ENum(2)), ENum(10))
  )

  def e8(body: Expr) = ELetRec(
    "power",
    EAscribe(
      ESLam("s",
        ELam("x", Some(TAt(TInt, SVar("s"))), ELam("n", Some(TInt), ECond1(
          EBinOp1("==", EVar("n"), ENum(0)),
          ELift(ENum(1), SVar("s")),
          EBinOp("*",
            EVar("x"),
            EApp1(EApp1(ESApp(EVar("power"), SVar("s")), EVar("x")), EBinOp1("-", EVar("n"), ENum(1))), SVar("s")),
        ), Some(TAt(TInt, SVar("s")))), Some(TInt))),
      TForallSt("s", TFun(TAt(TInt, SVar("s")), TFun(TInt, TAt(TInt, SVar("s")))))),
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
    EAscribe(
      ESLam("s",
        ELam("b", Some(TAt(TInt, SVar("s"))),
          ELam("n", Some(TInt),
            ELam("result", Some(TAt(TRef(TInt), SVar("s"))),
              ECond1(
                EBinOp1("==", EVar("n"), ENum(0)),
                EDeref(EVar("result"), SVar("s")),
                ELet("_", EAssign(EVar("result"), EBinOp("*", EVar("b"), EDeref(EVar("result"), SVar("s")), SVar("s")), SVar("s")),
                  EApp1(EApp1(EApp1(ESApp(EVar("impPower"), SVar("s")), EVar("b")), EBinOp1("-", EVar("n"), ENum(1))), EVar("result")))),
            Some(TAt(TInt, SVar("s")))), Some(TFun(TAt(TRef(TInt), SVar("s")), TAt(TInt, SVar("s"))))), Some(TAt(TInt, SVar("s"))))),
      TForallSt("s", TFun(TAt(TInt, SVar("s")), TFun(TInt, TFun(TRef(TInt), TAt(TInt, SVar("s"))))))),
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

  test("lam-app") {
    testEval(e1, "VCode(ELet(x2,ELam(x0,None,ELet(x1,EBinOp(+,EVar(x0),ENum(1),Some(SNum(1))),EVar(x1)),None),ELet(x3,EApp(EVar(x2),ENum(41),Some(SNum(1))),EVar(x3))))")

    testEval(e2, "VCode(ELet(x2,ELam(x0,None,ELet(x1,EBinOp(+,EVar(x0),ENum(1),Some(SNum(1))),EVar(x1)),None),EVar(x2)))")
  }

  test("cond") {
    testEval(e4, "VCode(ELet(x8,ECond(EBool(true),ELet(x2,ELam(x0,None,ELet(x1,EBinOp(+,EVar(x0),ENum(1),Some(SNum(1))),EVar(x1)),None),ELet(x3,EApp(EVar(x2),ENum(10),Some(SNum(1))),EVar(x3))),ELet(x6,ELam(x4,None,ELet(x5,EBinOp(*,EVar(x4),ENum(42),Some(SNum(1))),EVar(x5)),None),ELet(x7,EApp(EVar(x6),ENum(20),Some(SNum(1))),EVar(x7))),Some(SNum(1))),EVar(x8)))")
  }

  test("stage-poly") {
    testEval(e5(1), "VNum(6)")

    testEval(e5(2), "VCode(ELet(x2,ELam(x0,None,ELet(x1,EBinOp(+,EVar(x0),ENum(1),Some(SNum(1))),EVar(x1)),None),ELet(x3,EApp(EVar(x2),ENum(5),Some(SNum(1))),EVar(x3))))")

    val (VCode(e), _) = eval(e5(2))
    testEval(e, "VNum(6)")
  }

  test("rec") {
    testEval(e6, "VNum(120)")
    testEval(e7, "VNum(1024)")
  }

  test("rec-stage-poly") {
    testEval(e8(EApp1(EApp1(ESApp(EVar("power"), SNum(1)), ENum(2)), ENum(3))), "VNum(8)")

    testEval(e8(ELift2(ELam("x", Some(TCode(TInt)), EApp1(EApp1(ESApp(EVar("power"), SNum(2)), EVar("x")), ENum(3)), Some(TCode(TInt))))),
      "VCode(ELet(x4,ELam(x0,Some(TInt),ELet(x1,EBinOp(*,EVar(x0),ENum(1),Some(SNum(1))),ELet(x2,EBinOp(*,EVar(x0),EVar(x1),Some(SNum(1))),ELet(x3,EBinOp(*,EVar(x0),EVar(x2),Some(SNum(1))),EVar(x3)))),Some(TInt)),EVar(x4)))")

    val (VCode(e), _) = eval(e8(ELift2(ELam("x", Some(TCode(TInt)), EApp1(EApp1(ESApp(EVar("power"), SNum(2)), EVar("x")), ENum(3)), Some(TCode(TInt))))))
    testEval(EApp1(e, ENum(2)), "VNum(8)")
  }

  test("rec-imp-stage-poly") {
    testEval(e9(EApp1(EApp1(EApp1(ESApp(EVar("impPower"), SNum(1)), ENum(2)), ENum(3)), EAlloc1(ENum(1)))), "VNum(8)")

    testEval(e9(ELift2(ELam("x", Some(TCode(TInt)), EApp1(EApp1(EApp1(ESApp(EVar("impPower"), SNum(2)), EVar("x")), ENum(3)), EAlloc2(ELift2(ENum(1)))), Some(TCode(TInt))))),
      "VCode(ELet(x12,ELam(x0,Some(TInt),ELet(x1,EAlloc(ENum(1),Some(SNum(1))),ELet(x2,EDeref(EVar(x1),Some(SNum(1))),ELet(x3,EBinOp(*,EVar(x0),EVar(x2),Some(SNum(1))),ELet(x4,EAssign(EVar(x1),EVar(x3),Some(SNum(1))),ELet(x5,EDeref(EVar(x1),Some(SNum(1))),ELet(x6,EBinOp(*,EVar(x0),EVar(x5),Some(SNum(1))),ELet(x7,EAssign(EVar(x1),EVar(x6),Some(SNum(1))),ELet(x8,EDeref(EVar(x1),Some(SNum(1))),ELet(x9,EBinOp(*,EVar(x0),EVar(x8),Some(SNum(1))),ELet(x10,EAssign(EVar(x1),EVar(x9),Some(SNum(1))),ELet(x11,EDeref(EVar(x1),Some(SNum(1))),EVar(x11)))))))))))),Some(TInt)),EVar(x12)))")

    val (VCode(e), _) = eval(e9(ELift2(ELam("x", Some(TCode(TInt)), EApp1(EApp1(EApp1(ESApp(EVar("impPower"), SNum(2)), EVar("x")), ENum(3)), EAlloc2(ELift2(ENum(1)))), Some(TCode(TInt))))))
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
      "VCode(ELet(x8,EFix(f0,ELet(x7,ELam(x1,Some(TInt),ELet(x2,EBinOp(<=,EVar(x1),ENum(1),Some(SNum(1))),ELet(x6,ECond(EVar(x2),ENum(1),ELet(x3,EBinOp(-,EVar(x1),ENum(1),Some(SNum(1))),ELet(x4,EApp(EVar(f0),EVar(x3),Some(SNum(1))),ELet(x5,EBinOp(*,EVar(x1),EVar(x4),Some(SNum(1))),EVar(x5)))),Some(SNum(1))),EVar(x6))),Some(TInt)),EVar(x7)),Some(SNum(1))),ELet(x9,EApp(EVar(x8),ENum(5),Some(SNum(1))),EVar(x9))))")

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
            ELet(x2,EBinOp(+,EVar(x0),EVar(x1),Some(SNum(1))),EVar(x2)),None),
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
      "VCode(ELet(x2,ELam(x0,None,ELet(x1,EBinOp(+,EVar(x0),ENum(1),Some(SNum(1))),EVar(x1)),None),EVar(x2)))"
    )

    testEval(
      ERun(e1),
      "VClo(x0,None,ELet(x1,EBinOp(+,EVar(x0),ENum(1),Some(SNum(1))),EVar(x1)),None,Map(),Map())"
    )

    val e2 = ELet(
      "y",
      ELift2(ELam("x", None, EBinOp2("+", EVar("x"), ELift2(ENum(1))), None)),
      EApp2(EVar("y"), ELift2(ENum(1)))
    )

    testEval(
      e2,
      "VCode(ELet(x2,ELam(x0,None,ELet(x1,EBinOp(+,EVar(x0),ENum(1),Some(SNum(1))),EVar(x1)),None),ELet(x3,EApp(EVar(x2),ENum(1),Some(SNum(1))),EVar(x3))))"
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
