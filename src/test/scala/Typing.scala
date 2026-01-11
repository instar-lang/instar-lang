package spmp.tyck
import spmp.eff as core
import spmp.eff.Type
import spmp.eff.Stage

import spmp.surf.*

class TypingTest extends munit.FunSuite {

  test("subtype-simple") {
    import Subtyping.*
    import core.Type.*

    // int <: int
    assert(TInt.subtype(TInt, Set.empty))

    // bool <: bool
    assert(TBool.subtype(TBool, Set.empty))

    // unit <: unit
    assert(TUnit.subtype(TUnit, Set.empty))

    // int -> int <: int -> int
    assert(
      TFun(TInt, TInt)
        .subtype(TFun(TInt, TInt), Set.empty)
    )

    // int <: Code[int]
    assert(TInt.subtype(TCode(TInt), Set.empty))

    // Code[int] </: int
    assert(!TCode(TInt).subtype(TInt, Set.empty))

    // Code[int] -> Code[int] <: Code[int -> int]
    assert(
      TFun(TCode(TInt), TCode(TInt))
        .subtype(TCode(TFun(TInt, TInt)), Set.empty)
    )

    // Code[int] -> int <: Code[int -> int]
    assert(
      TFun(TCode(TInt), TInt)
        .subtype(TCode(TFun(TInt, TInt)), Set.empty)
    )

    // int -> Code[int] </: Code[int -> int]
    assert(
      !TFun(TInt, TCode(TInt))
        .subtype(TCode(TFun(TInt, TInt)), Set.empty)
    )
  }

  test("subtype-poly") {
    import Subtyping.*
    import core.Type.*
    import core.Stage.*

    // forall s. int <: forall s. int@s
    assert(
      TForallSt("s", TInt)
        .subtype(
          TForallSt("s", TAt(TInt, Stage.SVar("s"))),
          Set.empty
        )
    )

    // forall s. (int@s -> int@s) <: forall s. (int -> int)@s
    val s = SVar("s")
    assert(
      TForallSt("s", TFun(TAt(TInt, s), TAt(TInt, s)))
        .subtype(
          TForallSt("s", TAt(TFun(TInt, TInt), s)),
          Set.empty
        )
    )

    // forall s. int@s -> int <: forall s. (int -> int)@s
    assert(
      TForallSt("s", TFun(TAt(TInt, SVar("s")), TInt))
        .subtype(
          TForallSt("s", TAt(TFun(TInt, TInt), SVar("s"))),
          Set.empty
        )
    )

    // forall s1. int@s1 -> int <: forall s2. (int -> int)@s2
    val s1 = SVar("s1")
    val s2 = SVar("s2")
    assert(
      TForallSt("s1", TFun(TAt(TInt, s1), TInt))
        .subtype(
          TForallSt("s2", TAt(TFun(TInt, TInt), s2)),
          Set.empty
        )
    )

    // int </: forall s. int@s
    assert(
      !TInt.subtype(
        TForallSt("s", TAt(TInt, Stage.SVar("s"))),
        Set.empty
      )
    )

    // forall s. int@s </: forall s. Code[int]
    // TODO: Can we allow this subtyping relation?
    assert(
      !TForallSt("s", TAt(TInt, Stage.SVar("s"))).subtype(
        TForallSt("s", TCode(TInt)),
        Set.empty
      )
    )
  }

}
