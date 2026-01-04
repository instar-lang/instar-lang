package spmp.core.mono

import Stage.*
import Expr.*
import Type.*
import Value.*
import SubTyping.*

class MonoCoreTest extends munit.FunSuite {

  // run this test: sbt 'testOnly spmp.core.mono.MonoCoreTest'
  test("subtype") {
    // Subtype relations derived from reflexivity
    assert(TInt.subtype(TInt))
    assert(TFun(TInt, TInt, Top).subtype(TFun(TInt, TInt, Top)))
    assert(!TFun(TInt, TInt, Top).subtype(TFun(TBool, TInt, Top)))
    assert(!TFun(TInt, TInt, Top).subtype(TFun(TInt, TBool, Top)))

    // Let's say Rep[t1] <: Rep[t2] when t1 <: t2
    assert(TCode(TInt).subtype(TCode(TInt)))
    assert(!TCode(TBool).subtype(TCode(TInt)))
    // covariant in return type: Int -> Int <: Int -> Rep[Int]
    assert(TFun(TInt, TInt, Top).subtype(TFun(TInt, TCode(TInt), Top)))
    // contravariant in argument type: Rep[Int] -> Int <: Int -> Int
    assert(TFun(TCode(TInt), TInt, Top).subtype(TFun(TCode(TInt), TInt, Top)))

    // We can say t1 <: Rep[t2] when t1 <: t2, because we can always lift a value of t1 to get a value of Rep[t1]
    // Int <: Rep[Int]
    assert(TInt.subtype(TCode(TInt)))
    assert(!TBool.subtype(TCode(TInt)))

    // But the inverse is always not true. Because if somewhere expects a first stage value, it must not be given a second stage computation.
    // !(Rep[Int] <: Int)
    assert(!TCode(TInt).subtype(TInt))

  }

  test("bidirectional") {
    import spmp.surf.mono as surf
    import spmp.tyck.mono.*
    {
      // lift (λx: Rep[Int]. x + 1) ⇒ Rep[Int -> Int]
      val t = surf.Expr.ELift(
        surf.Expr.ELam(
          "x",
          Some(TCode(TInt)),
          surf.Expr.EBinOp(
            "+",
            surf.Expr.EVar("x"),
            surf.Expr.ENum(1)
          ),
          None
        )
      )

      val expected = TCode(
        TFun(
          TInt,
          TInt,
          Bot
        )
      )

      val inferred = Elab.infer(Map.empty, t)
      assertEquals(inferred.ty.get, expected)
    }

    {
      // (λx. x + 1) : Rep[Int]->Rep[Int] ⇒ Rep[Int]->Rep[Int]
      val t = surf.Expr
        .EAscribe(
          surf.Expr.ELam(
            "x",
            None,
            surf.Expr.EBinOp(
              "+",
              surf.Expr.EVar("x"),
              surf.Expr.ENum(1)
            ),
            None
          ),
          TFun(
            TCode(TInt),
            TCode(TInt),
            Bot
          )
        )

      val expected = TFun(
        TCode(TInt),
        TCode(TInt),
        Bot
      )
      val inferred = Elab.infer(Map.empty, t)
      assertEquals(inferred.ty.get, expected)
    }

    {
      // (lift (λx: Rep[Int]. x + 1)) 1 ⇒ Rep[Int]
      val t = surf.Expr.EApp(
        surf.Expr.ELift(
          surf.Expr.ELam(
            "x",
            Some(TCode(TInt)),
            surf.Expr.EBinOp(
              "+",
              surf.Expr.EVar("x"),
              surf.Expr.ENum(1)
            ),
            None
          )
        ),
        surf.Expr.ENum(1)
      )

      val expected = TCode(TInt)
      val inferred = Elab.infer(Map.empty, t)
      assertEquals(inferred.ty.get, expected)
    }

  }

}
