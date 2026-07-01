package instar.experiment.corebracket

import Stage.*
import Expr.*
import Type.*
import Value.*
import PreExpr.*

class CoreTest extends munit.FunSuite {

  def PApp1(e1: PreExpr, e2: PreExpr): PreExpr = PApp(e1, e2, Sta)
  def PApp2(e1: PreExpr, e2: PreExpr): PreExpr = PApp(e1, e2, Dyn)
  def PCond1(e1: PreExpr, e2: PreExpr, e3: PreExpr): PreExpr = PCond(e1, e2, e3, Sta)
  def PCond2(e1: PreExpr, e2: PreExpr, e3: PreExpr): PreExpr = PCond(e1, e2, e3, Dyn)
  def PBinOp1(op: String, e1: PreExpr, e2: PreExpr): PreExpr = PBinOp(op, e1, e2, Sta)
  def PBinOp2(op: String, e1: PreExpr, e2: PreExpr): PreExpr = PBinOp(op, e1, e2, Dyn)
  def PUnaryOp1(op: String, e: PreExpr): PreExpr = PUnaryOp(op, e, Sta)
  def PUnaryOp2(op: String, e: PreExpr): PreExpr = PUnaryOp(op, e, Dyn)

  val pStage1IncFn = PLam("x", None, PBinOp1("+", PVar("x"), PNum(1)        ), None)
  val eStage1IncFn = ELam("x", None, EBinOp1("+", EVar("x"), ENum(1)        ), None)
  val pStageSIncFn = PSLam("s", PLam("x", None, PBinOp("+", PVar("x"), PLift(PNum(1), SVar("s")), SVar("s")), None))
  val eStageSIncFn = ESLam("s", ELam("x", None, EBinOp("+", EVar("x"), ELift(ENum(1), SVar("s")), SVar("s")), None))
  
  // val e1 = PApp2(
  //   PLift2(
  //     PLam("x", None, PBinOp2("+", PNum("x"), PLift2(PNum(1))), None)
  //   ),
  //   PLift2(PNum(41))
  // )

  // val e2 = PLift2(
  //   PLam("x", None, PBinOp2("+", PNum("x"), PLift2(PNum(1))), None)
  // )

  // val e3 = PLift2(
  //   PLam("y", None, PBinOp2("*", PNum("y"), PLift2(PNum(42))), None)
  // )

  // val e4 = ECond(
  //   PLift2(EBool(true)),
  //   PApp2(e2, PLift2(PNum(10))),
  //   PApp2(e3, PLift2(PNum(20))),
  //   Dyn
  // )

  // def e5(stage: Int) = {
  //   // (Λs. (λx. x +ˢ 1ˢ)ˢ 5ˢ)[stage]
  //   val f = ESLam(
  //     "s",
  //     PApp(
  //       PLift(
  //         PLam(
  //           "x",
  //           None,
  //           PBinOp("+", PNum("x"), PLift(PNum(1), SVar("s")), SVar("s")),
  //           None
  //         ),
  //         SVar("s")
  //       ),
  //       PLift(PNum(5), SVar("s")),
  //       SVar("s")
  //     )
  //   )
  //   val arg = SNum(stage)
  //   ESApp(f, arg)
  // }

  def testEval(pe: PreExpr, str: String): Unit =
    val v = eval(pe)
    assertEquals(v.toString, str)

  def testTrans(pe: PreExpr, e: Expr): Unit =
    val pt = translate(pe)
    assertEquals(pt, e)

  test("prestranslation") {
    testTrans(PNum(1), ENum(1))
    testTrans(PBool(true), EBool(true))
    testTrans(PBinOp1("+", PNum(1), PNum(2)), 
              EBinOp1("+", ENum(1), ENum(2)))
    testTrans(PUnaryOp1("-", PNum(1)), EUnaryOp1("-", ENum(1)))
    testTrans(PVar("x"), EVar("x"))
    testTrans(PSLam("x", PBinOp1("+", PVar("x"), PNum(1))), 
              ESLam("x", EBinOp1("+", EVar("x"), ENum(1))))
    try { testTrans(PEscape(PUnit), EUnit); assert(false); }
    catch case e: Exception => ();

    // case PVar(name: String)
    // case PSLam(x: String, body: PreExpr)
    // case PSApp(e: PreExpr, st: Stage)
    // case PLam(x: String, argTy: Option[Type], body: PreExpr, retTy: Option[Type])
    // case PApp(e1: PreExpr, e2: PreExpr, st: Stage)
    // case PLift(t: PreExpr, to: Stage)
    // case PRun(t: PreExpr)
    // case PLet(x: String, rhs: PreExpr, body: PreExpr)
    // case PCond(e1: PreExpr, e2: PreExpr, e3: PreExpr, st: Stage)
    // case PBinOp(op: String, e1: PreExpr, e2: PreExpr, st: Stage)
    // case PUnaryOp(op: String, e: PreExpr, st: Stage)
    // case PAscribe(e: PreExpr, asTy: Type)
    // case PBracket(e: PreExpr)
    // case PEscape(e: PreExpr)
  }


  test("futTranslation") {
    testTrans(PBracket(PNum(1)), ELift2(ENum(1)))
    testTrans(PBracket(PVar("x")), EVar("x"))

    // lamb
    testTrans(PBracket(PLam("x", None, PBinOp1("+", PVar("x"), PNum(1)        ), None)),
              ELift2(  ELam("x", None, EBinOp2("+", EVar("x"), ELift2(ENum(1))), None)) )
    // app
    testTrans(PBracket(PApp(pStage1IncFn, PNum(1), Sta)),
              EApp2(ELift2(ELam("x", None, EBinOp2("+", EVar("x"), ELift2(ENum(1))), None)), ELift2(ENum(1)) ))

    // slam
    // testTrans(PBracket(pStageSIncFn), eStageSIncFn) // TODO this seems wrong
    // sapp
    // testTrans(PBracket(PSApp(pStageSIncFn, Sta)),
              //  ESApp(eStageSIncFn, Dyn))

    try { // translate should fail on a bracketed SApp @Dyn
      testTrans(PBracket(PSApp(pStageSIncFn, Dyn)), ESApp(eStageSIncFn, Dyn));
               assert(false)
    }
    catch case e: Exception => ();

    // case PSLam(x: String, body: PreExpr)
    // case PSApp(e: PreExpr, st: Stage)
    // case PLam(x: String, argTy: Option[Type], body: PreExpr, retTy: Option[Type])
    // case PApp(e1: PreExpr, e2: PreExpr, st: Stage)
    // case PLift(t: PreExpr, to: Stage)
    // case PRun(t: PreExpr)
    // case PLet(x: String, rhs: PreExpr, body: PreExpr)
    // case PCond(e1: PreExpr, e2: PreExpr, e3: PreExpr, st: Stage)
    // case PBinOp(op: String, e1: PreExpr, e2: PreExpr, st: Stage)
    // case PUnaryOp(op: String, e: PreExpr, st: Stage)
    // case PAscribe(e: PreExpr, asTy: Type)
    // case PBracket(e: PreExpr)
    // case PEscape(e: PreExpr)
  }

  // test("lam-app") {
  //   testEval(
  //     e1,
  //     "VCode(ELet(x2,PLam(x0,None,ELet(x1,PBinOp(+,PNum(x0),PNum(1),SNum(0)),PNum(x1)),None),ELet(x3,PApp(PNum(x2),PNum(41),SNum(0)),PNum(x3))))"
  //   )

  //   testEval(
  //     e2,
  //     "VCode(ELet(x2,PLam(x0,None,ELet(x1,PBinOp(+,PNum(x0),PNum(1),SNum(0)),PNum(x1)),None),PNum(x2)))"
  //   )
  // }

  // test("cond") {
  //   testEval(
  //     e4,
  //     "VCode(ELet(x8,ECond(EBool(true),ELet(x2,PLam(x0,None,ELet(x1,PBinOp(+,PNum(x0),PNum(1),SNum(0)),PNum(x1)),None),ELet(x3,PApp(PNum(x2),PNum(10),SNum(0)),PNum(x3))),ELet(x6,PLam(x4,None,ELet(x5,PBinOp(*,PNum(x4),PNum(42),SNum(0)),PNum(x5)),None),ELet(x7,PApp(PNum(x6),PNum(20),SNum(0)),PNum(x7))),SNum(0)),PNum(x8)))"
  //   )
  // }

  // test("stage-poly") {
  //   testEval(e5(0), "VNum(6)")

  //   testEval(
  //     e5(1),
  //     "VCode(ELet(x2,PLam(x0,None,ELet(x1,PBinOp(+,PNum(x0),PNum(1),SNum(0)),PNum(x1)),None),ELet(x3,PApp(PNum(x2),PNum(5),SNum(0)),PNum(x3))))"
  //   )

  //   val VCode(e) = eval(e5(1))
  //   testEval(e, "VNum(6)")
  // }

  // test("run") {
  //   testEval(PNum(1), "VNum(1)")

  //   testEval(ERun(PLift2(PNum(1))), "VNum(1)")

  //   val e1 =
  //     PLift2(PLam("x", None, PBinOp2("+", PNum("x"), PLift2(PNum(1))), None))

  //   testEval(
  //     e1,
  //     "VCode(ELet(x2,PLam(x0,None,ELet(x1,PBinOp(+,PNum(x0),PNum(1),SNum(0)),PNum(x1)),None),PNum(x2)))"
  //   )

  //   testEval(
  //     ERun(e1),
  //     "VClo(x0,None,ELet(x1,PBinOp(+,PNum(x0),PNum(1),SNum(0)),PNum(x1)),None,Map(),Map())"
  //   )

  //   val e2 = ELet(
  //     "y",
  //     PLift2(PLam("x", None, PBinOp2("+", PNum("x"), PLift2(PNum(1))), None)),
  //     PApp2(PNum("y"), PLift2(PNum(1)))
  //   )

  //   testEval(
  //     e2,
  //     "VCode(ELet(x2,PLam(x0,None,ELet(x1,PBinOp(+,PNum(x0),PNum(1),SNum(0)),PNum(x1)),None),ELet(x3,PApp(PNum(x2),PNum(1),SNum(0)),PNum(x3))))"
  //   )

  //   testEval(
  //     ERun(e2),
  //     "VNum(2)"
  //   )
  // }
}
