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
    assert(TFun(TInt, TInt).subtype(TFun(TInt, TInt)))
    assert(!TFun(TInt, TInt).subtype(TFun(TBool, TInt)))
    assert(!TFun(TInt, TInt).subtype(TFun(TInt, TBool)))

    // Let's say Rep[t1] <: Rep[t2] when t1 <: t2
    assert(TCode(TInt).subtype(TCode(TInt)))
    assert(!TCode(TBool).subtype(TCode(TInt)))
    // covariant in return type: Int -> Int <: Int -> Rep[Int]
    assert(TFun(TInt, TInt).subtype(TFun(TInt, TCode(TInt))))
    // contravariant in argument type: Rep[Int] -> Int <: Int -> Int
    assert(TFun(TCode(TInt), TInt).subtype(TFun(TCode(TInt), TInt)))

    // We can say t1 <: Rep[t2] when t1 <: t2, because we can always lift a value of t1 to get a value of Rep[t1]
    // Int <: Rep[Int]
    assert(TInt.subtype(TCode(TInt)))
    assert(!TBool.subtype(TCode(TInt)))

    // But the inverse is always not true. Because if somewhere expects a first stage value, it must not be given a second stage computation.
    // !(Rep[Int] <: Int)
    assert(!TCode(TInt).subtype(TInt))

  }

}
