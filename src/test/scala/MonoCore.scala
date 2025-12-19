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

}
