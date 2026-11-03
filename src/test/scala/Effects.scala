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
  test("identity coercions preserve primitive and function terms") {
    {
      val typed = infer(parse("(1: Int)"))
      assertEquals(pretty.expr(typed), "1")
      assertEquals(typed.ty, Some(TInt))
      assertEquals(typed.effect, Sta)
    }
    {
      val typed = infer(parse("(fun(x: Int) => x: Int -> Int)"))
      assertEquals(pretty.expr(typed), "fun(x: Int): Int => x")
      assertEquals(typed.ty, Some(TFun(TInt, TInt)))
      assertEquals(typed.effect, Sta)
    }
    {
      val typed = infer(parse("lift[1](fun(x: Int) => x)"))
      assertEquals(pretty.expr(typed), "fun(x: Int): Int => x")
      assertEquals(typed.ty, Some(TFun(TInt, TInt)))
      assertEquals(typed.effect, Sta)
    }
  }

  test("explicit effect casts preserve types and have no runtime action") {
    val typed = infer(parse("lift[2](1) |> 2"))
    assertEquals(pretty.expr(typed), "lift[2](1) |> 2")
    assertEquals(typed.ty, Some(TInt.at(Dyn)))
    assertEquals(typed.effect, Dyn)
    val checked = new CoreTyping().infer(typed)
    assertEquals(checked.effect, Dyn)
    assertEquals(instar.interp.eval(ERun(typed))._1, Value.VNum(1))
  }

  test("function promotion recursively promotes a static result") {
    val typed = infer(parse("lift[2](fun(x: Int@2) => 0)"))
    assertEquals(pretty.expr(typed),
      "let $s0 (x: Int @ 2): Int = 0 in fun@2($s1: Int @ 2): Int @ (2 | 1) => lift[(2 | 1)]($s0 $s1@1)")
    assert(Nil.implyTyEq(typed.ty.get, TFun(TInt.at(Dyn), TInt.at(Dyn)).at(Dyn)))
    assert(Nil.implyStEq(typed.effect, Dyn))
    val checked = new CoreTyping().infer(typed)
    assert(Nil.implyTyEq(checked.ty.get, typed.ty.get))
    assert(Nil.implyStEq(checked.effect, typed.effect))
    assertEquals(instar.interp.eval(infer(parse("run(lift[2](fun(x: Int@2) => 0)(3))")))._1,
      Value.VNum(0))
  }

  test("function coercion widens the latent effect with a body cast") {
    val typed = infer(parse("(fun(x: Int) => x: Int ->[2] Int)"))
    assertEquals(pretty.expr(typed),
      "let $s0 (x: Int): Int = x in lift[1](fun($s1: Int): Int => $s0 $s1@1 |> (((1 | 1) | 1) | 2))")
    assertEquals(typed.ty, Some(TFun(TInt, TInt, Dyn)))
    assert(Nil.implyStEq(typed.effect, Sta))
    val checked = new CoreTyping().infer(typed)
    assert(Nil.implyTyEq(checked.ty.get, typed.ty.get))
    assert(Nil.implyStEq(checked.effect, typed.effect))
  }

  test("forall coercion strengthens a contract and casts its body effect") {
    val typed = infer(parse("(sfun[s] => 7: forall[t: t <= 1]. Int)"))
    assertEquals(pretty.expr(typed),
      "let $s1[s] = 7 in sfun[$s2: $s2 <= 1] => $s1[$s2] |> 1")
    assert(Nil.implyTyEq(typed.ty.get, parseType("forall[t: t <= 1]. Int")))
    val checked = new CoreTyping().infer(typed)
    assert(Nil.implyTyEq(checked.ty.get, typed.ty.get))
    assert(Nil.implyStEq(checked.effect, typed.effect))
  }

  test("forall coercion permits a larger latent effect") {
    val typed = infer(parse("(sfun[s] => 1: forall[t] =>[2] Int)"))
    assertEquals(pretty.expr(typed), "let $s1[s] = 1 in sfun[$s2] => $s1[$s2] |> 2")
    assert(Nil.implyTyEq(typed.ty.get, parseType("forall[t] =>[2] Int")))
    val checked = new CoreTyping().infer(typed)
    assert(Nil.implyTyEq(checked.ty.get, typed.ty.get))
    assert(Nil.implyStEq(checked.effect, typed.effect))
  }

  test("ordinary function headers infer their latent effects") {
    val typed = infer(parse("let f(x: Int): Int@2 = x in f"))
    assertEquals(pretty.expr(typed),
      "let f (x: Int): Int @ 2 = lift[2](x) in f")
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

  test("forall coercion converts its result under the target contract") {
    val typed = infer(parse("(sfun[s] => 1: forall[t] =>[t] Int@t)"))
    assertEquals(pretty.expr(typed),
      "let $s1[s] = 1 in sfun[$s2] => lift[$s2]($s1[$s2]) |> $s2")
    assert(Nil.implyTyEq(typed.ty.get, parseType("forall[t] =>[t] Int@t")))
    val checked = new CoreTyping().infer(typed)
    assert(Nil.implyTyEq(checked.ty.get, typed.ty.get))
    assert(Nil.implyStEq(checked.effect, typed.effect))
    assertEquals(instar.interp.eval(infer(parse("run((sfun[s] => 1: forall[t] =>[t] Int@t)[2])")))._1,
      Value.VNum(1))
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
      "letrec@1 f ($s0: Int): Int @ 2 = (fun(x: Int): Int @ 2 => lift[2](x)) $s0@1 |> (((1 | 2) | 1) | 2) in f")
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

  test("forall coercion cannot weaken a required contract") {
    intercept[TypeException] { infer(parse("(sfun[s: s <= 1] => 1: forall[t]. Int)")) }
    intercept[TypeException] { infer(parse("(sfun[s] => lift[s](1): forall[t]. Int@t)")) }
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
