package instar.experiment.corebracket

import Stage.*
import Expr.*
import Type.*
import Value.*
import PreExpr.*
import instar.bracketparser.parse

class TransTest extends munit.FunSuite {

  def testTrans(pe: PreExpr, e: Expr): Unit =
    val pt = translate(pe)
    assertEquals(pt, e)
  def testTransFails(pe: PreExpr): Unit = 
    try { translate(pe); assert(false); }
    catch case e: TranslationException => ();

  val pStage1IncFn = PLam("x", None, PBinOp1("+", PVar("x"), PNum(1)), None)
  val eStage1IncFn = ELam("x", None, EBinOp1("+", EVar("x"), ENum(1)), None)
  val eStage2IncFn = ELam("x", None, EBinOp2("+", EVar("x"), ENum(1)), None)
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



  test("trans-unbracketed-boring") {
    testTrans(PNum(1), ENum(1))
    testTrans(PBool(true), EBool(true))
    testTrans(PBinOp1("+", PNum(1), PNum(2)), 
              EBinOp1("+", ENum(1), ENum(2)))
    testTrans(PUnaryOp1("-", PNum(1)), EUnaryOp1("-", ENum(1)))
    testTrans(PLet("x", PUnit, PVar("x")), ELet("x", EUnit, EVar("x")))
    testTrans(PLam("x", None, PBinOp1("+", PVar("x"), PNum(1)), None), 
              ELam("x", None, EBinOp1("+", EVar("x"), ENum(1)), None) )
    testTrans(PSLam("s", pStageSIncFn),
              ESLam("s", eStageSIncFn))
  }
  
  test("trans-invalid-toplevel") {
    testTransFails(PEscape(PUnit))
  }

  test("trans-bracketed-boring") {
    testTrans(PBracket(PNum(1)), ELift2(ENum(1)))

    // lamb
    testTrans(PBracket(PLam("x", None, PBinOp1("+", PVar("x"), PNum(1)        ), None)),
              ELift2(  ELam("x", None, EBinOp2("+", EVar("x"), ELift2(ENum(1))), None)) )
    // app
    testTrans(PBracket(PApp(pStage1IncFn, PNum(1), Sta)),
              EApp2(ELift2(ELam("x", None, EBinOp2("+", EVar("x"), ELift2(ENum(1))), None)), ELift2(ENum(1)) ))

  }

  test("trans-bracketed-let") {
    testTrans(PBracket(PLet("x", PUnit, PVar("x"))), ELet("x", ELift2(EUnit), EVar("x")))
  }

  test("trans-bracketed-lambda") {
    testTrans(PBracket(pStage1IncFn), ELift2(ELam("x", None, EBinOp2("+", EVar("x"), ELift2(ENum(1))), None)))
  }

  test("trans-stat-vars-in-brackets") {
    testTrans(PLet("x", PUnit, PBracket(PVar("x"))), ELet("x", EUnit, ELift2(EVar("x"))))
  }

  test("trans-dyn-vars-in-escape") {
    testTransFails( PBracket(PLet("x", PUnit, PEscape(PVar("x")))))
    testTransFails( PBracket(PLam("x", None, PEscape(PVar("x")), None)) )
  }

  test("trans-no-spoly-in-brackets") {
      testTransFails( PBracket(PSApp(pStageSIncFn, Dyn)) )
      testTransFails( PBracket(PSLam("s", PLam("x", None, PVar("x"), None))) )
  }

  test("escapes") {
    // TODO slam splice...
  }


}

class EvalTest extends munit.FunSuite {

  def testEval(pe: PreExpr, str: String): Unit =
    val v = eval(pe)
    assertEquals(v.toString, str)
  def testEvalFails(pe: PreExpr): Unit = 
    try { eval(pe); assert(false); }
    catch case e: Exception => ();


  val pStage1IncFn = PLam("x", None, PBinOp1("+", PVar("x"), PNum(1)), None)
  val eStage1IncFn = ELam("x", None, EBinOp1("+", EVar("x"), ENum(1)), None)
  val pStage2IncFn = PLift2(PLam("x", None, PBinOp2("+", PVar("x"), PNum(1)), None))
  val eStage2IncFn = ELift2(ELam("x", None, EBinOp2("+", EVar("x"), ENum(1)), None))
  val pStageSIncFn = PSLam("s", PLam("x", None, PBinOp("+", PVar("x"), PLift(PNum(1), SVar("s")), SVar("s")), None))
  val eStageSIncFn = ESLam("s", ELam("x", None, EBinOp("+", EVar("x"), ELift(ENum(1), SVar("s")), SVar("s")), None))

  test("eval-unbracketed-boring") {
    testEval(PNum(1), "VNum(1)")
    testEval(PBool(true), "VBool(true)")
    testEval(PBinOp1("+", PNum(1), PNum(2)), "VNum(3)")
    testEval(PUnaryOp1("-", PNum(1)), "VNum(-1)")
    testEval(PLet("x", PUnit, PVar("x")), "VUnit")
    testEval(pStage1IncFn, eval(eStage1IncFn).toString)
    testEval(PSLam("s", pStageSIncFn), eval(ESLam("s", eStageSIncFn)).toString)
  }

  test("eval-bracketed-boring") {
    testEval(PBracket(PNum(1)), "VCode(ENum(1))")
    testEval(
      PBracket(PBinOp1("+", PNum(1), PNum(2))),
      "VCode(ELet(x0,EBinOp(+,ENum(1),ENum(2),SNum(0)),EVar(x0)))"
    )
    testEval(PBracket(pStage1IncFn), 
      "VCode(" +
        "ELet(" +
          "x2,ELam(x0,None,ELet(x1,EBinOp(+,EVar(x0),ENum(1),SNum(0)),EVar(x1)),None)," +
          "EVar(x2)" +
        ")" +
      ")"
    )
    testEval(
      PBracket(pStage1IncFn), 
      eval(ELift2(ELam("x", None, EBinOp2("+", EVar("x"), ELift2(ENum(1))), None))).toString
    )
    testEval(PBracket(PApp(pStage1IncFn, PNum(1), Sta)), 
      "VCode(" +
        "ELet(" +
          "x2,ELam(x0,None,ELet(x1,EBinOp(+,EVar(x0),ENum(1),SNum(0)),EVar(x1)),None)," +
          "ELet(" +
            "x3,EApp(EVar(x2),ENum(1),SNum(0))," +
            "EVar(x3)" +
          ")" +
        ")" +
      ")"
    )
    // testEval(
    //   PBracket(PApp(pStage1IncFn, PNum(1), Sta)),
    //   eval(EApp(eStage2IncFn, ENum(1), Dyn)).toString()
    // )
  }

}

class ParseTest extends munit.FunSuite {
  def testParse(str: String, pe: PreExpr): Unit =
    val v = parse(str)
    assertEquals(v.toString, str)

  test("basics") {
    testParse(
      "if (1 == 1) then 1 else 1",
      PCond1(PBinOp1("=", PNum(1), PNum(1)), 
            PNum(1), 
            PNum(1))
    )
  }
}