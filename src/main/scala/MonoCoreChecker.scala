package spmp.core.mono

import spmp.core.mono.*

type TypeEnv = Map[String, Type]

object SubTyping:
  extension (t1: Type)
    // Subtyping relation: t1 <: t2
    def subtype(t2: Type): Boolean = (t1, t2) match
      case (Type.TFun(Type.TCode(arg1), Type.TCode(ret1), _), Type.TCode(Type.TFun(arg2, ret2, _))) =>
        arg2.subtype(arg1) && ret1.subtype(ret2)
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
      case (Type.TBool, Type.TCode(Type.TBool)) |
          (Type.TUnit, Type.TCode(Type.TUnit)) |
          (Type.TInt, Type.TCode(Type.TInt)) =>
        // bool <: Rep[bool]
        // unit <: Rep[unit]
        // int  <: Rep[int]
        true
      case (Type.TCode(a), b) =>
        false
      case (a, b) if a == b =>
        // reflexivity, we must put this case after TCode cases, because TCode(TUnit).subtype(TCode(TUnit)) is false
        true
      case _ => false
      // Q: Can we say Rep[t1] <: t2?
      // A: No, and it's not similar as previous case.
      //    The only way to bring a value of Rep[t1] to a first stage value of t1 is to `run` it.
      //    But I (DZ) think inserting `lift` when needed is natural, but inserting `run` is weird.
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

def join(t1: Type, t2: Type): Type =
  import SubTyping.*
  // TODO: implement join correctly
  if t1.subtype(t2) then t2
  else if t2.subtype(t1) then t1
  else
    // no join type
    throw new Exception(
      s"Join type for the case of $t1 and $t2 is not supported yet."
    )
