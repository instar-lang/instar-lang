package spmp.core.mono

import spmp.core.mono.*

type TypeEnv = Map[String, Type]

object SubTyping:
  extension (t1: Type)
    // Subtyping relation: t1 <: t2
    def subtype(t2: Type): Boolean = (t1, t2) match
      case (Type.TFun(arg1, ret1, _), Type.TFun(arg2, ret2, _)) =>
        // contravariant in argument, covariant in return
        // FIXME: relation between the latent effects?
        arg2.subtype(arg1) && ret1.subtype(ret2)
      case (Type.TCode(t1), Type.TCode(t2)) => // Rep[t1] <: Rep[t2]
        // Q: What is Rep[t1]?
        // A: A first stage value with type Rep[t1] represents second stage computation that returns t1.
        // Q: When a value of Rep[t1] be used as Rep[t2], so we can have Rep[t1] <: Rep[t2]?
        // A: I (DZ) think it depends on what our type system wants to guarantee for the user. But at least t1 <: t2.
        if !t1.subtype(t2) then false
        else {
          // Q: When we cannot say Rep[t1] <: Rep[t2], even if we have t1 <: t2?
          // A: I (DZ) cannot find out a case for now.
          true
        }
      case (a, Type.TCode(b)) => // t1 <: Rep[t2]
        // Q: When a value of t1 can replace every usage of another value of Rep[t2]?
        // A: Anytime if t1 <: t2. Because we can always apply operator `lift` on a value of t1 to get Rep[t1].
        a.subtype(b)
      case (Type.TCode(a), b) =>
        // Q: Can we say Rep[t1] <: t2?
        // A: No, and it's not similar as previous case.
        //    The only way to bring a value of Rep[t1] to a first stage value of t1 is to `run` it.
        //    But I (DZ) think inserting `lift` when needed is natural, but inserting `run` is weird.
        false
      case (a, b) if a == b =>
        // reflexivity, we must put this case after TCode cases, because TCode(TUnit).subtype(TCode(TUnit)) is false
        true
      case _ => false

    def isPure: Boolean =
      // I (DZ) don't now how to detect impurity in current setting, so let's conservatively say computation with any type could be impure.
      false

def isFirstStage(t: Type): Boolean = t match
  case Type.TUnit => true
  case Type.TInt  => true
  case Type.TBool => true
  case Type.TFun(arg, ret, _) =>
    isFirstStage(arg) && isFirstStage(ret)
  case Type.TCode(_) => false

def check(expr: Expr, env: TypeEnv): Unit = {
  import SubTyping.*
  // We assume that all expressions are already fully annotated with types in
  // its `ty` field. This function just checks the consistency of these annotations.
  expr match
    case Expr.EUnit      => assert(expr.ty.get == Type.TUnit)
    case Expr.ENum(i)    => assert(expr.ty.get == Type.TInt)
    case Expr.EBool(b)   => assert(expr.ty.get == Type.TBool)
    case Expr.EVar(name) => assert(env(name) == expr.ty.get)
    case Expr.ELam(x, body) =>
      val Type.TFun(expectedArgTy, expectedRetTy, _) = expr.ty.get
      check(body, env + (x -> expectedArgTy))
    // case Expr.ELam(x, body) =>
    //   val Type.TFun(expectedArgTy, expectedRetTy) = expr.ty.get
    //   check(body, env + (x -> expectedArgTy))
    case Expr.EApp(e1, e2, st) =>
      // check the annotations are consistent
      val Type.TFun(argTy, retTy, _) = e1.ty.get
      assert(e2.ty.get.subtype(argTy))
      assert(expr.ty.get == retTy)
      check(e1, env)
      check(e2, env)
    case Expr.ELift(t) =>
      check(t, env)
      val ty = t.ty.get
      // ty must be a first stage type
      assert(isFirstStage(ty))
      val expectedTy = Type.TCode(ty)
      assert(expr.ty.get == expectedTy)
    case Expr.ERun(t) =>
      check(t, env)
      val Type.TCode(ty) = t.ty.get
      // ty must be a TCode or TFrag type
      assert(expr.ty.get == ty)
    case Expr.ELet(x, rhs, body) =>
      check(rhs, env)
      check(body, env + (x -> rhs.ty.get))
    case Expr.ECond(e1, e2, e3, st) =>
      check(e1, env)
      assert(e1.ty.get == Type.TBool)
      check(e2, env)
      check(e3, env)
      assert(e2.ty.get == expr.ty.get)
      assert(e3.ty.get == expr.ty.get)
    case Expr.EBinOp(op, e1, e2, st) =>
      op match
        case "+" | "-" | "*" | "/" =>
          assert(e1.ty.get == Type.TInt)
          assert(e2.ty.get == Type.TInt)
          assert(expr.ty.get == Type.TInt)
        case "==" | "!=" | "<" | "<=" | ">" | ">=" =>
          assert(e1.ty.get == Type.TInt)
          assert(e2.ty.get == Type.TInt)
          assert(expr.ty.get == Type.TBool)
    case Expr.EUnaryOp(op, e, st) =>
      op match
        case "-" =>
          assert(e.ty.get == Type.TInt)
          assert(expr.ty.get == Type.TInt)
}

// We can derive infer function for the cases where above check function directly asserts
// the ty field of expr. Becase that field holds the type information we want to fill in during type checking.
def infer(expr: Expr, env: TypeEnv): Expr = {
  import SubTyping.*
  expr match
    case Expr.EUnit                       => expr.withType(Type.TUnit)
    case Expr.ENum(i)                     => expr.withType(Type.TInt)
    case Expr.EBool(b)                    => expr.withType(Type.TBool)
    case Expr.EVar(name)                  => expr.withType(env(name))
    case Expr.ELam(x, body) =>
      // we cannot infer the argument and return types without argument type annotation
      // argTy match {
      //   case None =>
      //     // If no argument type annotation, we cannot infer the type of a lambda
      //     ???
      //   case Some(argTy) =>
      //     val bodyTyped = infer(body, env + (x -> argTy))
      //     retTy.foreach(t => assert(t == bodyTyped.ty.get))
      //     val expectedTy = Type.TFun(argTy, bodyTyped.ty.get)
      //     assert(expr.ty.get == expectedTy)
      //     Expr.ELam(x, Some(argTy), bodyTyped, bodyTyped.ty).withType(expectedTy)
      // }
      ???
    case Expr.EApp(e1, e2, st) =>
      val e1Typed = infer(e1, env)
      val e2Typed = infer(e2, env)
      val Type.TFun(argTy, retTy, _) = e1Typed.ty.get
      assert(e2Typed.ty.get.subtype(argTy))
      Expr.EApp(e1Typed, e2Typed, st).withType(retTy)
    case Expr.ELift(t) =>
      val tTyped = infer(t, env)
      val ty = tTyped.ty.get
      // ty must be a first stage type
      assert(isFirstStage(ty))
      val expectedTy = Type.TCode(ty)
      Expr.ELift(tTyped).withType(expectedTy)
    case Expr.ERun(t) =>
      val tTyped = infer(t, env)
      val Type.TCode(ty) = tTyped.ty.get
      Expr.ERun(tTyped).withType(ty)
    case Expr.ELet(x, rhs, body) =>
      val rhsTyped = infer(rhs, env)
      infer(body, env + (x -> rhsTyped.ty.get))
    case Expr.ECond(e1, e2, e3, st) =>
      val e1Tyed = infer(e1, env)
      assert(e1Tyed.ty.get == Type.TBool)
      val e2Typed = infer(e2, env)
      val e3Typed = infer(e3, env)
      assert(e2Typed.ty.get == e3Typed)
      e2Typed
    case Expr.EBinOp(op, e1, e2, st) =>
      op match
        case "+" | "-" | "*" | "/" =>
          val e1Typed = infer(e1, env)
          val e2Typed = infer(e2, env)
          assert(e1Typed.ty.get == Type.TInt)
          assert(e2Typed.ty.get == Type.TInt)
          Expr.EBinOp(op, e1Typed, e2Typed, st).withType(Type.TInt)
        case "==" | "!=" | "<" | "<=" | ">" | ">=" =>
          val e1Typed = infer(e1, env)
          val e2Typed = infer(e2, env)
          assert(e1Typed.ty.get == Type.TInt)
          assert(e2Typed.ty.get == Type.TInt)
          Expr.EBinOp(op, e1Typed, e2Typed, st).withType(Type.TBool)
    case Expr.EUnaryOp(op, e, st) =>
      op match
        case "-" =>
          val eTyped = infer(e, env)
          assert(eTyped.ty.get == Type.TInt)
          Expr.EUnaryOp(op, eTyped, st).withType(Type.TInt)
}
