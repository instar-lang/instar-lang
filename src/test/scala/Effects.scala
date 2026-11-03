package instar.typing

import munit.FunSuite
import instar.interp.Value
import instar.parser.{parse, parseType}
import instar.pretty
import instar.syntax.*
import Expr.*
import Stage.*
import Type.*
import StageConstraints.*
import Elaboration.infer

class EffectElaborationTest extends FunSuite:

  test("explicit effect casts preserve types and have no runtime action") {
    val typed = infer(parse("lift[2](1) |> 2"))
    assertEquals(pretty.expr(typed), "lift[2](1) |> 2")
    assertEquals(typed.ty, Some(TInt.at(Dyn)))
    assertEquals(typed.effect, Dyn)
    val checked = new CoreTyping().infer(typed)
    assertEquals(checked.effect, Dyn)
    assertEquals(instar.interp.eval(ERun(typed))._1, Value.VNum(1))
  }

  test("function coercion widens the latent effect with a body cast") {
    val typed = infer(parse("(fun(x: Int) => x: Int ->[2] Int)"))
    assertEquals(pretty.expr(typed),
      "let $s0 (x: Int): Int = x in lift[1](fun($s1: Int): Int => lift[1]($s0 (lift[1]($s1))@1) |> (case(1, " +
      "((case(1, 1, case(1, 2, 1)) | 1) | 1), case(1, 2, ((case(1, 1, case(1, 2, 1)) | 1) | 1))) | 2))")
    assertEquals(typed.ty, Some(TFun(TInt, TInt, Dyn)))
    assert(Nil.implyStEq(typed.effect, Sta))
    val checked = new CoreTyping().infer(typed)
    assert(Nil.implyTyEq(checked.ty.get, typed.ty.get))
    assert(Nil.implyStEq(checked.effect, typed.effect))
  }

  test("ordinary function headers infer their latent effects") {
    val typed = infer(parse("let f(x: Int): Int@2 = x in f"))
    assertEquals(pretty.expr(typed),
      "let f (x: Int): Int @ 2 = lift[2](x) in let $s0 = f in lift[1](fun($s1: Int): Int @ 2 => lift[2]($s0 " +
      "(lift[1]($s1))@1) |> (case(2, ((case(1, 1, case(1, 2, 1)) | case(2, 1, case(1, 2, 1))) | 1), case(2, 2, " +
      "((case(1, 1, case(1, 2, 1)) | case(2, 1, case(1, 2, 1))) | 1))) | case(2, 1, case(1, 2, 1))))")
    assert(Nil.implyTyEq(typed.ty.get, TFun(TInt, TInt.at(Dyn), Dyn)))
    assert(Nil.implyStEq(typed.effect, Sta))
    val checked = new CoreTyping().infer(typed)
    assert(Nil.implyTyEq(checked.ty.get, typed.ty.get))
    assert(Nil.implyStEq(checked.effect, typed.effect))
  }

  test("stage cases select their branch during staging") {
    val typed = infer(parse("lift[case(1, 2, 1)](1)"))
    assertEquals(pretty.expr(typed),
      "lift[case(1, 2, 1)](1)")
    assert(Nil.implyTyEq(typed.ty.get, TInt.at(Dyn)))
    assert(Nil.implyStEq(typed.effect, Dyn))
    assertEquals(instar.interp.eval(ERun(typed))._1, Value.VNum(1))
  }

  test("stage application substitutes latent effects") {
    val typed = infer(parse("(sfun[s] => fun(x: Int) => lift[s](x))[2]"))
    assertEquals(pretty.expr(typed), "(sfun[s] => fun(x: Int): Int @ s => lift[s](x))[2]")
    assert(Nil.implyTyEq(typed.ty.get, TFun(TInt, TInt.at(Dyn), Dyn)))
    assert(Nil.implyStEq(typed.effect, Sta))
    val checked = new CoreTyping().infer(typed)
    assert(Nil.implyTyEq(checked.ty.get, typed.ty.get))
  }

  test("recursive signatures permit a larger body effect") {
    val typed = infer(parse("fix f: Int ->[2] Int@2. fun(x: Int) => lift[2](x)"))
    assertEquals(pretty.expr(typed),
      "letrec@1 f ($s2: Int): Int @ 2 = (let $s0 (x: Int): Int @ 2 = lift[2](x) in lift[1](fun($s1: Int): Int @" +
      " 2 => lift[2]($s0 (lift[1]($s1))@1) |> (case(2, ((case(1, 1, case(1, 2, 1)) | case(2, 1, case(1, 2, 1)))" +
      " | 1), case(2, 2, ((case(1, 1, case(1, 2, 1)) | case(2, 1, case(1, 2, 1))) | 1))) | 2))) $s2@1 |> ((((1 " +
      "| 1) | 2) | 1) | 2) in let $s3 = f in lift[1](fun($s4: Int): Int @ 2 => lift[2]($s3 (lift[1]($s4))@1) |>" +
      " (case(2, ((case(1, 1, case(1, 2, 1)) | 2) | 1), case(2, 2, ((case(1, 1, case(1, 2, 1)) | 2) | 1))) | " +
      "2))")
    assert(Nil.implyTyEq(typed.ty.get, TFun(TInt, TInt.at(Dyn), Dyn)))
    val checked = new CoreTyping().infer(typed)
    assert(Nil.implyTyEq(checked.ty.get, typed.ty.get))
    assert(Nil.implyStEq(checked.effect, typed.effect))
  }

class EffectNegativeTest extends FunSuite:
  test("effect casts cannot decrease an effect") {
    intercept[TypeException] { infer(parse("lift[2](1) |> 1")) }
    intercept[TypeException] { new CoreTyping().infer(parse("lift[2](1) |> 1")) }
  }

  test("function coercion cannot conceal a latent effect") {
    intercept[TypeException] { infer(parse("(fun(x: Int) => lift[2](x): Int -> Int@2)")) }
    intercept[TypeException] { infer(parse("fun(f: (Int@2 ->[2] Int@2)@2) => f")) }
  }

  test("recursive signatures bound body effects and retain result annotations") {
    intercept[TypeException] { infer(parse("fix f: Int -> Int@2. fun(x: Int) => lift[2](x)")) }
    intercept[TypeException] { infer(parse("fix f: Int -> Int. fun(x: Int): Bool => x")) }
  }

  test("effects and compound stages must be scoped") {
    intercept[TypeException] { infer(parse("fun(x: Int ->[missing] Int) => x")) }
    intercept[TypeException] { infer(parse("lift[1 | missing](1)")) }
    intercept[TypeException] { infer(parse("1 |> case(missing, 1, 2)")) }
  }
