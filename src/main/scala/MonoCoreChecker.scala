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

def max(t1: Type, t2: Type): Type =
  import SubTyping.*
  if t1.subtype(t2) then t2
  else if t2.subtype(t1) then t1
  else
    // no max type
    throw new Exception(s"No max type for $t1 and $t2")

def check(expr: Expr, expected: Type, env: TypeEnv): Unit = {
  import SubTyping.*
  // TODO: handle effect checking
  expr match
    case Expr.ELam(x, body) =>
      expected match
        case Type.TFun(argTy, retTy, _) =>
          // Γ, x:argTy ⊢ body ⇐ retTy
          // --------------------------------
          // Γ ⊢ λx.body ⇐ argTy → retTy
          check(body, retTy, env + (x -> argTy))
        case Type.TCode(Type.TFun(argTy, retTy, _)) =>
          // Γ, x:Code[argTy] ⊢ body ⇐ Code[retTy]
          // --------------------------------
          // Γ ⊢ λx.body ⇐ Code[argTy → retTy] (principal judgement)

          // TODO: Should Code[argTy] → Code[retTy] be a subtype of Code[argTy → retTy]?
          // Since we can always do lift(Code[argTy] → Code[retTy]) to get Code[argTy → retTy].
          check(body, Type.TCode(retTy), env + (x -> Type.TCode(argTy)))
    case Expr.EApp(e1, e2, _st) =>
      // Γ ⊢ e1 ⇒ argTy → retTy
      // Γ ⊢ e2 ⇐ argTy
      // retTy <: expected
      // ------------------------
      // Γ ⊢ e1 e2 ⇐ retTy

      // TODO (DZ): I think it's could be possible to do η-expansion here if
      // e1's type is Code[argTy → retTy], but let's not do it for now.

      val e1Typed = infer(e1, env)
      val Type.TFun(argTy, retTy, _) = e1Typed.ty.get
      assert(e2.ty.get.subtype(argTy))
      assert(expr.ty.get == retTy)
      check(e2, argTy, env)
    case Expr.ELift(t) =>
      // This is a introduction rule for TCode type, the conclusion is the principal judgement.
      // Γ ⊢ e ⇐ ty
      // -----------------------
      // Γ ⊢ lift e ⇐ TCode[ty] (principal judgement)
      val Type.TCode(ty) = expected
      check(t, ty, env)
    case Expr.ERun(t) =>
      // Elimination rule for TCode type.
      // Γ ⊢ t ⇐ TCode[ty]
      // -----------------------
      // Γ ⊢ run t ⇐ ty

      // TODO (DZ): According to the bidirectional typing recipe, the premise
      // judgement should be an inference judgement. But I (DZ) think we should
      // also make a check judgement here so that the expected type information can
      // flow into t and don't stuck.
      assert(isFirstStage(expected))
      check(t, Type.TCode(expected), env)
    case Expr.ELet(x, rhs, body) =>
      // Γ ⊢ rhs ⇒ ty
      // Γ, x:ty ⊢ body ⇐ expected
      // --------------------------------
      // Γ ⊢ let x = rhs in body ⇐ expected
      val rhsTyped = infer(rhs, env)
      check(body, expected, env + (x -> rhsTyped.ty.get))
    case Expr.ECond(e1, e2, e3, _st) =>
      // This is an elimination rule for Bool or Code[Bool]


      // we need to infer e1, because we don't know whether it's Bool or Code[Bool]
      val e1Typed = infer(e1, env)
      e1Typed.ty.get match
        case Type.TCode(Type.TBool) =>
          // Γ ⊢ e1 ⇒ Code[Bool]
          // Γ ⊢ e2 ⇐ expected
          // Γ ⊢ e3 ⇐ expected
          // ------------------------------------------
          // Γ ⊢ if e1 then e2 else e3 ⇐ expected
          check(e2, expected, env)
          check(e3, expected, env)
        case Type.TBool =>
          // Γ ⊢ e1 ⇒ Bool
          // Γ ⊢ e2 ⇐ expected
          // Γ ⊢ e3 ⇐ expected
          // ------------------------------------------
          // Γ ⊢ if e1 then e2 else e3 ⇐ expected
          check(e2, expected, env)
          check(e3, expected, env)
        case _ =>
          assert(
            false,
            s"Condition expression must have type Bool or Code[Bool], but got ${e1Typed.ty.get}"
          )
    case Expr.EBinOp(op, e1, e2, _st) =>
      op match
        case "+" | "-" | "*" | "/" =>
          // We don't know the st in the surface language, so we ignore it here
          // Γ ⊢ e1 ⇐ T
          // Γ ⊢ e2 ⇐ T
          // T <: Code[Int]
          // -----------------------
          // Γ ⊢ e1 op_2 e2 ⇐ T
          check(e1, Type.TInt, env)
          check(e2, Type.TInt, env)
        case "==" | "!=" | "<" | "<=" | ">" | ">=" =>
          // Γ ⊢ e1 ⇐ f(T)
          // Γ ⊢ e2 ⇐ f(T)
          // T <: Code[Bool]
          // where f(Code[T]) = Code[T]
          //       f(T) = T
          // -----------------------
          // Γ ⊢ e1 op_2 e2 ⇐ T
          check(e1, expected, env)
          check(e2, expected, env)
    case Expr.EUnaryOp(op, e, _st) =>
      assert(expected.subtype(Type.TCode(Type.TInt)))
      op match
        case "-" =>
          // Γ ⊢ e ⇐ T
          // T <: Code[Int]
          // -----------------------
          // Γ ⊢ op_1 e ⇐ T
          check(e, expected, env)
    case Expr.EUnit | Expr.ENum(_) | Expr.EBool(_) | Expr.EVar(_) =>
      // Apply the change direction rule for these primitive expressions.
      // According to the bidirectional recipe, we should change direction as
      // late as possible so the information of expected type can be preserved
      // more.

      // Γ ⊢ expr ⇒ ty
      // ty <: expected
      // -----------------------
      // Γ ⊢ expr ⇐ expected
      val typed = infer(expr, env)
      assert(expr.ty.get.subtype(typed.ty.get))
}

// We can derive infer function for the cases where above check function directly asserts
// the ty field of expr. Becase that field holds the type information we want to fill in during type checking.
def infer(expr: Expr, env: TypeEnv): Expr = {
  import SubTyping.*
  expr match
    case Expr.EUnit         => expr.withType(Type.TUnit)
    case Expr.ENum(i)       => expr.withType(Type.TInt)
    case Expr.EBool(b)      => expr.withType(Type.TBool)
    case Expr.EVar(name)    => expr.withType(env(name))
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
      e1Typed.ty.get match
        case Type.TCode(Type.TFun(argTy, retTy, _)) =>
          // Γ ⊢ e1 ⇒ Code[argTy → retTy]
          // Γ ⊢ e2 ⇐ Code[argTy]
          // ------------------------
          // Γ ⊢ e1 e2 ⇒ Code[retTy]
          check(e2, Type.TCode(argTy), env)
          Expr.EApp(e1Typed, e2, st).withType(Type.TCode(retTy))
        case Type.TFun(argTy, retTy, _) =>
          // Γ ⊢ e1 ⇒ argTy → retTy
          // Γ ⊢ e2 ⇐ argTy
          // ------------------------
          // Γ ⊢ e1 e2 ⇒ retTy
          check(e2, argTy, env)
          Expr.EApp(e1Typed, e2, st).withType(retTy)
    case Expr.ELift(t) =>
      // Γ ⊢ e ⇒ ty
      // -----------------------
      // Γ ⊢ lift e ⇒ TCode[ty]
      val tTyped = infer(t, env)
      val ty = tTyped.ty.get
      // ty must be a first stage type
      assert(isFirstStage(ty))
      Expr.ELift(tTyped).withType(Type.TCode(ty))
    case Expr.ERun(t) =>
      // Γ ⊢ t ⇒ TCode[ty]
      // -----------------------
      // Γ ⊢ run t ⇒ ty
      val tTyped = infer(t, env)
      val Type.TCode(ty) = tTyped.ty.get
      Expr.ERun(tTyped).withType(ty)
    case Expr.ELet(x, rhs, body) =>
      // Γ ⊢ rhs ⇒ ty
      // Γ, x:ty ⊢ body ⇒ bodyTy
      // --------------------------------
      // Γ ⊢ let x = rhs in body ⇒ bodyTy
      val rhsTyped = infer(rhs, env)
      infer(body, env + (x -> rhsTyped.ty.get))
    case Expr.ECond(e1, e2, e3, st) =>
      // We need to infer e1 to know whether it's Bool or Code[Bool] (same as in check)
      val e1Typed = infer(e1, env)
      e1Typed.ty.get match
        case Type.TCode(Type.TBool) | Type.TBool =>
          // Γ ⊢ e1 ⇒ Code[Bool]
          // Γ ⊢ e2 ⇒ ty
          // Γ ⊢ e3 ⇒ ty
          // ----------------------------------
          // Γ ⊢ if e1 then e2 else e3 ⇒ ty

          // Γ ⊢ e1 ⇒ Bool
          // Γ ⊢ e2 ⇒ ty
          // Γ ⊢ e3 ⇒ ty
          // ------------------------
          // Γ ⊢ if e1 then e2 else e3 ⇒ ty

          val e2Typed = infer(e2, env)
          val e3Typed = infer(e3, env)
          Expr
            .ECond(e1Typed, e2Typed, e3Typed, st)
            .withType(max(e2Typed.ty.get, e3Typed.ty.get))
    case Expr.EBinOp(op, e1, e2, st) =>
      op match
        case "+" | "-" | "*" | "/" =>
          // Γ ⊢ e1 ⇒ T1
          // Γ ⊢ e2 ⇒ T2
          // T1 ⊔ T2 <: Code[Int]
          // -----------------------
          // Γ ⊢ e1 op_2 e2 ⇒ T1 ⊔ T2

          val e1Typed = infer(e1, env)
          assert(e1Typed.ty.get.subtype(Type.TCode(Type.TInt)))
          val e2Typed = infer(e2, env)
          assert(e2Typed.ty.get.subtype(Type.TCode(Type.TInt)))
          Expr.EBinOp(op, e1Typed, e2Typed, st).withType(max(e1Typed.ty.get, e2Typed.ty.get))
        case "==" | "!=" | "<" | "<=" | ">" | ">=" =>
          // Γ ⊢ e1 ⇒ T1
          // Γ ⊢ e2 ⇒ T2
          // T1 ⊔ T2 = Code[Int]
          // -----------------------
          // Γ ⊢ e1 op_2 e2 ⇒ Code[Bool]

          // Γ ⊢ e1 ⇒ T1
          // Γ ⊢ e2 ⇒ T2
          // T1 ⊔ T2 = Int
          // -----------------------
          // Γ ⊢ e1 op_2 e2 ⇒ Bool
          val e1Typed = infer(e1, env)
          val e2Typed = infer(e2, env)
          max(e1Typed.ty.get, e2Typed.ty.get) match
            case Type.TCode(Type.TInt) =>
              Expr.EBinOp(op, e1Typed, e2Typed, st).withType(Type.TCode(Type.TBool))
            case Type.TInt =>
              Expr.EBinOp(op, e1Typed, e2Typed, st).withType(Type.TBool)
    case Expr.EUnaryOp(op, e, st) =>
      op match
        case "-" =>
          val eTyped = infer(e, env)
          assert(eTyped.ty.get.subtype(Type.TCode(Type.TInt)))
          Expr.EUnaryOp(op, eTyped, st).withType(eTyped.ty.get)
}
