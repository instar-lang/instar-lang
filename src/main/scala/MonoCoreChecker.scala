package spmp.core.mono

import spmp.core.mono.*

type TypeEnv = Map[String, Type]

def isFirstStage(t: Type): Boolean = t match
  case Type.TUnit         => true
  case Type.TInt          => true
  case Type.TBool         => true
  case Type.TFun(arg, ret) =>
    isFirstStage(arg) && isFirstStage(ret)
  case Type.TFrag(_) => false
  case Type.TRep(_)  => false

def check(expr: Expr, env: TypeEnv): Unit = {
  // We assume that all expressions are already fully annotated with types in
  // its `ty` field. This function just checks the consistency of these annotations.
  expr match
    case Expr.EUnit      => assert(expr.ty.get == Type.TUnit)
    case Expr.ENum(i)    => assert(expr.ty.get == Type.TInt)
    case Expr.EBool(b)   => assert(expr.ty.get == Type.TBool)
    case Expr.EVar(name) => assert(env(name) == expr.ty.get)
    case Expr.ELam(x, argTy, body, retTy) =>
      val Type.TFun(expectedArgTy, expectedRetTy) = expr.ty.get
      argTy.foreach(t => assert(t == expectedArgTy))
      assert(body.ty.get == expectedRetTy)
      check(body, env + (x -> expectedArgTy))
    case Expr.EApp(e1, e2, st) =>
      // check the annotations are consistent
      val Type.TFun(argTy, retTy) = e1.ty.get
      assert(e2.ty.get == argTy)
      assert(expr.ty.get == retTy)
      check(e1, env)
      check(e2, env)
    case Expr.ELift(t) =>
      check(t, env)
      val ty = t.ty.get
      // ty must be a first stage type
      assert(isFirstStage(ty))
      val expectedTy = Type.TRep(ty)
      assert(expr.ty.get == expectedTy)
    case Expr.ERun(t) =>
      check(t, env)
      val ty = t.ty.get
      // ty must be a TRep or TFrag type
      ty match
        case Type.TRep(inner) =>
          assert(expr.ty.get == inner)
        case Type.TFrag(inner) =>
          assert(expr.ty.get == inner)
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
    case Expr.EUnaryOp(op, e, st)    =>
      op match
        case "-" =>
          assert(e.ty.get == Type.TInt)
          assert(expr.ty.get == Type.TInt)
    case Expr.EAscribe(e, _)         =>
      // todo: remove this case later
      check(e, env)
      assert(e.ty.get == expr.ty.get)
}
