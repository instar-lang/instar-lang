package spmp.tyck
import spmp.eff as core
import spmp.eff.Type
import spmp.eff.Stage

import spmp.surf.*
import spmp.Counter.reset

class TypingTest extends munit.FunSuite {

  test("subtype-simple") {
    import Subtyping.*
    import core.Type.*

    // int <: int
    TInt.subtype(TInt, EmptyStEnv)

    // bool <: bool
    TBool.subtype(TBool, EmptyStEnv)

    // unit <: unit
    TUnit.subtype(TUnit, EmptyStEnv)

    // int -> int <: int -> int
    TFun(TInt, TInt)
      .subtype(TFun(TInt, TInt), EmptyStEnv)

    // int <: Code[int]
    TInt.subtype(TCode(TInt), EmptyStEnv)

    // Code[int] </: int
    intercept [SubtypeError] {
      TCode(TInt).subtype(TInt, EmptyStEnv)
    }

    // Code[int] -> Code[int] <: Code[int -> int]
    TFun(TCode(TInt), TCode(TInt))
      .subtype(TCode(TFun(TInt, TInt)), EmptyStEnv)

    // Code[int] -> int <: Code[int -> int]
    TFun(TCode(TInt), TInt)
      .subtype(TCode(TFun(TInt, TInt)), EmptyStEnv)

    // int -> Code[int] </: Code[int -> int]
    intercept [SubtypeError] {
      TFun(TInt, TCode(TInt))
        .subtype(TCode(TFun(TInt, TInt)), EmptyStEnv)
    }
  }

  test("subtype-poly") {
    import Subtyping.*
    import core.Type.*
    import core.Stage.*

    // forall s. int <: forall s. int@s
    TForallSt("s", TInt)
      .subtype(
        TForallSt("s", TAt(TInt, Stage.SVar("s"))),
        EmptyStEnv
      )

    // forall s. (int@s -> int@s) <: forall s. (int -> int)@s
    val s = SVar("s")
    TForallSt("s", TFun(TAt(TInt, s), TAt(TInt, s)))
      .subtype(
        TForallSt("s", TAt(TFun(TInt, TInt), s)),
        EmptyStEnv
      )

    // forall s. int@s -> int <: forall s. (int -> int)@s
    TForallSt("s", TFun(TAt(TInt, SVar("s")), TInt))
      .subtype(
        TForallSt("s", TAt(TFun(TInt, TInt), SVar("s"))),
        EmptyStEnv
      )

    // forall s1. int@s1 -> int <: forall s2. (int -> int)@s2
    val s1 = SVar("s1")
    val s2 = SVar("s2")
    TForallSt("s1", TFun(TAt(TInt, s1), TInt))
      .subtype(
        TForallSt("s2", TAt(TFun(TInt, TInt), s2)),
        EmptyStEnv
      )

    // int </: forall s. int@s
    intercept [SubtypeError] {
      TInt.subtype(
        TForallSt("s", TAt(TInt, Stage.SVar("s"))),
        EmptyStEnv
      )
    }

    // forall s. int@s </: forall s. Code[int]
    // TODO: Can we make allow this subtyping relation?
    intercept [SubtypeError] {
      TForallSt("s", TAt(TInt, Stage.SVar("s"))).subtype(
        TForallSt("s", TCode(TInt)),
        EmptyStEnv
      )
    }

    // { s } ⊢ int <: int@s
    TInt.subtype(TAt(TInt, SVar("s")), EmptyStEnv.addSVar("s"))
  }

  def testCoerce(
      expr: core.Expr,
      from: core.Type,
      to: core.Type,
      expected: String
  ) = {
    import Subtyping.*
    reset
    val coerced = expr.coerceTo(from, to, EmptyStEnv)
    assertEquals(coerced.toString, expected)
  }

  test("subtype-coerce-simple") {
    import Subtyping.*
    import core.Type.*

    val expr = core.Expr.EVar("f")

    // int <: int
    testCoerce(
      expr,
      TInt,
      TInt,
      "EVar(f)"
    )

    // int -> int <: int -> int
    testCoerce(
      expr,
      TFun(TInt, TInt),
      TFun(TInt, TInt),
      "ELam(x0,Some(TInt),EApp(EVar(f),EVar(x0),SNum(0)),Some(TInt))"
    )

    // int <: Code[int]
    testCoerce(
      expr,
      TInt,
      TCode(TInt),
      "ELift(EVar(f),SNum(1))"
    )

    // Code[int] -> Code[int] <: Code[int -> int]
    // f: Code[int] -> Code[int] ⊢ f ⇐ Code[int -> int] ~> lift (λ x: Code[int]. (f x): Code[int])
    testCoerce(
      expr,
      TFun(TCode(TInt), TCode(TInt)),
      TCode(TFun(TInt, TInt)),
      "ELift(ELam(x0,Some(TCode(TInt)),EApp(EVar(f),EVar(x0),SNum(0)),Some(TCode(TInt))),SNum(1))"
    )

    // Code[int] -> int <: Code[int -> int]
    // f: Code[int] -> int ⊢ f ⇐ Code[int -> int] ~> lift (λ x: Code[int]. (lift (f x)) : Code[int])
    testCoerce(
      expr,
      TFun(TCode(TInt), TInt),
      TCode(TFun(TInt, TInt)),
      "ELift(ELam(x0,Some(TCode(TInt)),ELift(EApp(EVar(f),EVar(x0),SNum(0)),SNum(1)),Some(TCode(TInt))),SNum(1))"
    )
  }

  test("subtype-coerce-poly") {
    import Subtyping.*
    import core.Type.*
    import core.Stage.*

    val expr = core.Expr.EVar("f")

    // forall s. int <: forall s. int@s
    // f: forall s. int ⊢ f ⇐ forall s. int@s ~> Λs. lift (f[s], s)
    testCoerce(
      expr,
      TForallSt("s", TInt),
      TForallSt("s", TAt(TInt, SVar("s"))),
      "ESLam(s0,ELift(ESApp(EVar(f),SVar(s0)),SVar(s0)))"
    )

    // forall s. (int@s -> int@s) <: forall s. (int -> int)@s
    // f: forall s. (int@s -> int@s) ⊢ f ⇐ forall s. (int -> int)@s ~> Λs. lift (λ x: int@s. (f[s] x), s)
    val s = SVar("s")
    testCoerce(
      expr,
      TForallSt("s", TFun(TAt(TInt, s), TAt(TInt, s))),
      TForallSt("s", TAt(TFun(TInt, TInt), s)),
      "ESLam(s0,ELift(ELam(x1,Some(TAt(TInt,SVar(s0))),EApp(ESApp(EVar(f),SVar(s0)),EVar(x1),SNum(0)),Some(TAt(TInt,SVar(s0)))),SVar(s0)))"
    )

    // forall s. int@s -> int <: forall s. (int -> int)@s
    // f: forall s. int@s -> int ⊢ f ⇐ forall s. (int -> int)@s ~> Λs. lift (λ x: int@s. lift (f[s] x, s), s)
    testCoerce(
      expr,
      TForallSt("s", TFun(TAt(TInt, SVar("s")), TInt)),
      TForallSt("s", TAt(TFun(TInt, TInt), SVar("s"))),
      "ESLam(s0,ELift(ELam(x1,Some(TAt(TInt,SVar(s0))),ELift(EApp(ESApp(EVar(f),SVar(s0)),EVar(x1),SNum(0)),SVar(s0)),Some(TAt(TInt,SVar(s0)))),SVar(s0)))"
    )
  }

  def testInfer(e: Expr, str: String): Unit = {
    reset
    val (eTyped, stenv) = infer(Map.empty, EmptyStEnv, e)
    assertEquals(eTyped.ty.get.toString, str)
  }

  test("typing-mono") {
    import core.Type.*
    import core.Stage.*
    import Expr.*

    // λx: int. x + 1 ⇒ int -> int
    val e0 = ELam(
      "x",
      TInt,
      EBin("+", EVar("x"), ENatV(1))
    )
    testInfer(e0, "TFun(TInt,TInt)")

    // lift (1, Dyn) ⇒ Code[int]
    val e1 = ELift(ENatV(1), core.Dyn)
    testInfer(e1, "TCode(TInt)")

    // lift (λx: Code[int]. x, Dyn) ⇒ Code[int -> int]
    val e2 = ELift(ELam("x", TCode(TInt), EVar("x")), core.Dyn)
    testInfer(e2, "TCode(TFun(TInt,TInt))")

    // ifz 0 then 1 else (2 : Code[int])
    val e3 = EIfz(ENatV(0), ENatV(1), EAscribe(ENatV(2), TCode(TInt)))
    testInfer(e3, "TCode(TInt)")

    // if 0 then (1: Code[int]) else 2
    val e4 = EIfz(
      ENatV(0),
      EAscribe(ENatV(1), TCode(TInt)),
      ENatV(2)
    )
    testInfer(e4, "TCode(TInt)")

    intercept[MatchError] {
      // if lift(0) then 1 else 2
      val e5 = EIfz(
        ELift(ENatV(0), core.Dyn),
        ENatV(1),
        ENatV(2)
      )
      testInfer(e5, "")
    }
  }

  test("typing-poly") {
    import core.Type.*
    import core.Stage.*
    import Expr.*

    // Λs. λx: int. x ⇒ ∀s. int → int
    val e0 = ESLam(
      "s",
      ELam("x", TInt, EVar("x"))
    )
    testInfer(e0, "TForallSt(s,TFun(TInt,TInt))")

    // Λs. λx: int@s. x + 1 ⇒ ∀s. int@s → int@s
    val e1 = ESLam(
      "s",
      ELam("x", TAt(TInt, SVar("s")), EBin("+", EVar("x"), ENatV(1)))
    )
    testInfer(e1, "TForallSt(s,TFun(TAt(TInt,SVar(s)),TAt(TInt,SVar(s))))")

    // Λs. lift (1, s) ⇒ ∀s. int@s
    val e2 = ESLam("s", ELift(ENatV(1), SVar("s")))
    testInfer(e2, "TForallSt(s,TAt(TInt,SVar(s)))")

    // Λs. lift (λx: int@s. x, s) ⇒ ∀s. (int -> int)@s
    val e3 = ESLam(
      "s",
      ELift(
        ELam("x", TAt(TInt, SVar("s")), EVar("x")),
        SVar("s")
      )
    )
    testInfer(e3, "TForallSt(s,TAt(TFun(TInt,TInt),SVar(s)))")

    // Λs. λx: int@s. λy: int. x + y ⇒ ∀s. int@s -> int -> int@s
    val e4 = ESLam(
      "s",
      ELam(
        "x",
        TAt(TInt, SVar("s")),
        ELam(
          "y",
          TInt,
          EBin("+", EVar("x"), EVar("y"))
        )
      )
    )
    testInfer(
      e4,
      "TForallSt(s,TFun(TAt(TInt,SVar(s)),TFun(TInt,TAt(TInt,SVar(s)))))"
    )

    // ⊢ fix power: ∀s. int@s -> int -> int@s = Λs. λx: int@s. λn: int. ifz n then 1@s else x * (power[s] (n - 1))
    // ⇒ ∀s. int@s -> int -> int@s
    val e5 = EFix(
      "power",
      TForallSt(
        "s",
        TFun(
          TAt(TInt, SVar("s")),
          TFun(
            TInt,
            TAt(TInt, SVar("s"))
          )
        )
      ),
      ESLam(
        "s",
        ELam(
          "x",
          TAt(TInt, SVar("s")),
          ELam(
            "n",
            TInt,
            EIfz(
              EVar("n"),
              ELift(ENatV(1), SVar("s")),
              EBin(
                "*",
                EVar("x"),
                EApp(
                  EApp(
                    ESApp(EVar("power"), SVar("s")),
                    EVar("x")
                  ),
                  EBin("-", EVar("n"), ENatV(1))
                )
              )
            )
          )
        )
      )
    )
    testInfer(
      e5,
      "TForallSt(s,TFun(TAt(TInt,SVar(s)),TFun(TInt,TAt(TInt,SVar(s)))))"
    )

    intercept[MatchError] {
      // lift λx: Code[int]. Λs. 1ˢ
      val e6 = ELift(
        ELam(
          "x",
          TCode(TInt),
          ESLam(
            "s",
            ELift(ENatV(1), SVar("s"))
          )
        ),
        core.Dyn
      )
      testInfer(e6, "")
    }
  }

}
