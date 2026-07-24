package instar.experiment.corebracket

import Stage.*
import Expr.*
import Type.*
import Value.*
import PreExpr.*

class TransTest extends munit.FunSuite {

  def testTrans(pe: PreExpr, e: Expr): Unit =
    val pt = translate(pe)
    assertEquals(pt, e)
  def testTransFails(pe: PreExpr): Unit =
    try { translate(pe); assert(false); }
    catch case e: TranslationException => ();

  def ELift2(e: Expr) = ELift(e, Dyn)
  val pStage1IncFn = PLam("x", None, PBinOp1("+", PVar("x"), PNum(1)), None)
  val eStage1IncFn = ELam("x", None, EBinOp1("+", EVar("x"), ENum(1)), None)
  val eStage2IncFn = ELam("x", None, EBinOp2("+", EVar("x"), ENum(1)), None)
  val pStageSIncFn = PSLam(
    "s",
    PLam(
      "x",
      None,
      PBinOp("+", PVar("x"), PLift(PNum(1), SVar("s")), SVar("s")),
      None
    )
  )
  val eStageSIncFn = ESLam(
    "s",
    ELam(
      "x",
      None,
      EBinOp("+", EVar("x"), ELift(ENum(1), SVar("s")), SVar("s")),
      None
    )
  )

  test("trans-unbracketed-boring") {
    testTrans(PNum(1), ENum(1))
    testTrans(PBool(true), EBool(true))
    testTrans(PBinOp1("+", PNum(1), PNum(2)), EBinOp1("+", ENum(1), ENum(2)))
    testTrans(PUnaryOp1("-", PNum(1)), EUnaryOp1("-", ENum(1)))
    testTrans(PLet("x", PUnit, PVar("x")), ELet("x", EUnit, EVar("x")))
    testTrans(
      PLam("x", None, PBinOp1("+", PVar("x"), PNum(1)), None),
      ELam("x", None, EBinOp1("+", EVar("x"), ENum(1)), None)
    )
    testTrans(PSLam("s", pStageSIncFn), ESLam("s", eStageSIncFn))
  }

  test("trans-invalid-toplevel") {
    testTransFails(PEscape(PUnit))
  }

  test("trans-bracketed-boring") {
    testTrans(PBracket(PNum(1)), ELift2(ENum(1)))

    // lamb
    testTrans(
      PBracket(PLam("x", None, PBinOp1("+", PVar("x"), PNum(1)), None)),
      ELift2(ELam("x", None, EBinOp2("+", EVar("x"), ELift2(ENum(1))), None))
    )
    // app
    testTrans(
      PBracket(PApp(pStage1IncFn, PNum(1), Sta)),
      EApp2(
        ELift2(ELam("x", None, EBinOp2("+", EVar("x"), ELift2(ENum(1))), None)),
        ELift2(ENum(1))
      )
    )

  }

  test("trans-bracketed-let") {
    testTrans(
      PBracket(PLet("x", PUnit, PVar("x"))),
      ELet("x", ELift2(EUnit), EVar("x"))
    )
  }

  test("trans-bracketed-lambda") {
    testTrans(
      PBracket(pStage1IncFn),
      ELift2(ELam("x", None, EBinOp2("+", EVar("x"), ELift2(ENum(1))), None))
    )
  }

  test("trans-stat-vars-in-brackets") {
    testTrans(
      PLet("x", PUnit, PBracket(PVar("x"))),
      ELet("x", EUnit, ELift2(EVar("x")))
    )
  }

  test("trans-dyn-vars-in-escape") {
    testTransFails(PBracket(PLet("x", PUnit, PEscape(PVar("x")))))
    testTransFails(PBracket(PLam("x", None, PEscape(PVar("x")), None)))
  }

  test("trans-no-spoly-in-brackets") {
    testTransFails(PBracket(PSApp(pStageSIncFn, Dyn)))
    testTransFails(PBracket(PSLam("s", PLam("x", None, PVar("x"), None))))
  }

  test("nested brackets fail") {
    // '('( () ))
    testTransFails(
      PBracket(PBracket(PUnit))
    )
  }

    // '($($( () ))
  test("too many escapes fail") {
    testTransFails(
      PBracket(PEscape(PEscape(PUnit)))
    )
  }

  test("bracket escape weaving") {
    // '($('($('( () ))))) = lift( () )
    // this is actually right
    testTrans(
      PBracket(PEscape(PBracket(PEscape(PBracket(PUnit))))),
      ELift2(EUnit)
    )
  }

  test("mixed brackets and lifts") {
    // '( let f = $(lift(fun x => x) in f x ) = let f = lift(fun x => x) in lift(f 1)
    testTrans(
      PBracket(PLet("f", 
        PEscape(PLift2(PLam("x", None, PVar("x"), None))),
         PApp1(PVar("f"), PNum(1)))),
      ELet("f", 
        ELift2(ELam("x", None, EVar("x"), None)), 
        EApp2(EVar("f"), ELift2(ENum(1))))
    )
  }

  test("mixed spoly and lifts") {
    // let f[s] (x) = x +@s 1 in '( $(f[2] 1) * 2 ) 
    // = let f[s] (x) = x +@s 1 in (f[2] 1) *@2 lift 2 -- and that fn call is st 1
    testTrans(
      PLet("f", 
        PSLam("s", 
          PLam("x", None, PBinOp("+", PVar("x"), PNum(1), SVar("s")), None)),
        PBracket(
          PBinOp1("*", 
            PEscape(
              PApp1(
                PSApp(PVar("f"), Dyn),
                PNum(1)
              )
            ),
            PNum(2)
          )
        )
      ),
      ELet("f", 
        ESLam("s", 
          ELam("x", None, EBinOp("+", EVar("x"), ENum(1), SVar("s")), None)),
        EBinOp2("*", 
          EApp1(
            ESApp(EVar("f"), Dyn),
            ENum(1)
          ),
          ELift2(ENum(2))
        )
      )
    )

    // let f[s] (x) = x +@s 1 in '(let g = $(lift f[2]) in g 1) 
    // = let f[s] (x) = x +@s 1 in let g = lift(f[2]) in g 1 -- but stage 2 app
    testTrans(
      PLet("f", 
        PSLam("s", 
          PLam("x", None, PBinOp("+", PVar("x"), PNum(1), SVar("s")), None),
        ),
        PBracket(
          PLet("g", 
          PEscape(PLift2(PSApp(PVar("f"), Dyn))),
          PApp1(PVar("g"), PNum(1))
          )
        )
      ),
      ELet("f", 
        ESLam("s", 
          ELam("x", None, EBinOp("+", EVar("x"), ENum(1), SVar("s")), None)
        ),
        ELet("g", 
          ELift2(ESApp(EVar("f"), Dyn)),
          EApp2(EVar("g"), ELift2(ENum(1)))
        )
      )
    )
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
  val pStage2IncFn = PLift2(
    PLam("x", None, PBinOp2("+", PVar("x"), PNum(1)), None)
  )
  val eStage2IncFn = ELift2(
    ELam("x", None, EBinOp2("+", EVar("x"), ENum(1)), None)
  )
  val pStageSIncFn = PSLam(
    "s",
    PLam(
      "x",
      None,
      PBinOp("+", PVar("x"), PLift(PNum(1), SVar("s")), SVar("s")),
      None
    )
  )
  val eStageSIncFn = ESLam(
    "s",
    ELam(
      "x",
      None,
      EBinOp("+", EVar("x"), ELift(ENum(1), SVar("s")), SVar("s")),
      None
    )
  )

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
    testEval(
      PBracket(pStage1IncFn),
      "VCode(" +
        "ELet(x2," +
          "ELam(x0," +
            "None," +
            "ELet(x1,EBinOp(+,EVar(x0),ENum(1),SNum(0)),EVar(x1))," +
            "None)," +
          "EVar(x2)))"
    )
    testEval(
      PBracket(pStage1IncFn),
      eval(
        ELift2(ELam("x", None, EBinOp2("+", EVar("x"), ELift2(ENum(1))), None))
      ).toString
    )
    testEval(
      PBracket(PApp(pStage1IncFn, PNum(1), Sta)),
      "VCode(" +
          "ELet(x2," +
            "ELam(x0,None,ELet(x1,EBinOp(+,EVar(x0),ENum(1),SNum(0)),EVar(x1)),None)," +
            "ELet(x3," +
              "EApp(EVar(x2),ENum(1),SNum(0))," +
              "EVar(x3))))"
    )
  }

  test("mixed spoly and lifts") {
    // let f[s] (x) = x +@s 1 in '( $(f[2] 1) * 2 ) 
    val e1 = PLet("f", 
      PSLam("s", 
        PLam("x", None, PBinOp("+", PVar("x"), PLift(PNum(1), SVar("s")), SVar("s")), None)
      ),
      PBracket(
        PBinOp("*", 
          PEscape(
            PApp(PSApp(PVar("f"), Dyn),
            PLift(PNum(1), Dyn), Sta)
          ),
          PNum(2), Sta
        )
      )
    )

    // e1 -> "let x0 = 1 + 1 in let x1 = x0 * 2 in x1"
    testEval(
      e1,
      "VCode("+
        "ELet(x0,EBinOp(+,ENum(1),ENum(1),SNum(0))," +
        "ELet(x1," +
          "EBinOp(*,EVar(x0),ENum(2),SNum(0))," +
          "EVar(x1))))"
    )
    // run e1 -> 4
    testEval(PRun(e1), "VNum(4)")

    // let f[s] (x) = x +@s 1 in '(let g = $(lift f[2]) in g 1) 
    val e2 = PLet("f",
      PSLam("s", 
        PLam("x", None, PBinOp("+", PVar("x"), PLift(PNum(1), SVar("s")), SVar("s")), None)
      ),
      PBracket(
        PLet("g", 
          PEscape(PLift2(PSApp(PVar("f"), Dyn))),
          PApp1(PVar("g"), PNum(1))
        )
      )
    )
    // e2 -> "let x2 = (fun x0 => let x1 = x0 + 1 in x1) in
    //        let x2 = x0 1 in x2"
    testEval(
      e2,
      "VCode(" +
        "ELet(x2," +
          "ELam(x0,None," +
            "ELet(x1," +
              "EBinOp(+,EVar(x0),ENum(1),SNum(0))," +
              "EVar(x1))," +
            "None)," +
          "ELet(x3," +
            "EApp(EVar(x2),ENum(1),SNum(0))," +
            "EVar(x3))))"
    )
    // run e2 -> 4
    testEval(PRun(e2), "VNum(2)")

  }
}
