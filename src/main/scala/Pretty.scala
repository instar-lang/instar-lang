package instar.pretty

import scala.collection.mutable.ArrayBuffer

import instar.interp.Value
import instar.interp.Value.*
import instar.syntax.*
import Expr.*
import Stage.*
import Type.*

private enum HeaderBinder:
  case Stage(name: String)
  case Term(name: String, ty: Option[Type])

def expr(expr: Expr): String =
  renderExpr(expr, 0)

def value(value: Value): String =
  value match
    case VCode(t) => expr(t)
    case VUnit => "()"
    case VNum(i) => i.toString
    case VBool(b) => b.toString
    case VLoc(loc) => s"loc($loc)"
    case VSClo(st, _, _, _) => s"<stage-closure:$st>"
    case VClo(x, _, _, _, _, _) => s"<closure:$x>"
    case VBNClo(x, _, _, _, _, _) => s"<cbn-closure:$x>"
    case VThunk(_, _, _) => "<thunk>"

private def renderExpr(expr: Expr, parentPrec: Int): String =
  expr match
    case ELet(x, rhs, body) =>
      extractHeader(rhs) match
        case Some((binders, retTy, coreBody)) =>
          s"let $x${renderHeader(binders)}${renderReturn(retTy)} = ${renderExpr(coreBody, 0)} in ${renderExpr(body, 0)}"
        case None =>
          s"let $x = ${renderExpr(rhs, 0)} in ${renderExpr(body, 0)}"

    case ELetRec(f, rhs, body) =>
      extractHeader(rhs) match
        case Some((binders, retTy, coreBody)) =>
          s"letrec $f${renderHeader(binders)}${renderReturn(retTy)} = ${renderExpr(coreBody, 0)} in ${renderExpr(body, 0)}"
        case None =>
          s"letrec $f = ${renderExpr(rhs, 0)} in ${renderExpr(body, 0)}"

    case ECond(e1, e2, e3, st) =>
      maybeParens(
        s"if${renderStageValue(st)} ${renderExpr(e1, 0)} then ${renderExpr(e2, 0)} else ${renderExpr(e3, 0)}",
        parentPrec > 0,
      )

    case ELam(x, argTy, body, retTy) =>
      val arg = argTy.map(renderType(_, 0)).getOrElse("_")
      maybeParens(
        s"fun($x: $arg)${renderReturn(retTy)} => ${renderExpr(body, 0)}",
        parentPrec > 0,
      )

    case EBNLam(x, argTy, body, retTy) =>
      val arg = argTy.map(renderType(_, 0)).getOrElse("_")
      maybeParens(
        s"fun!($x: $arg)${renderReturn(retTy)} => ${renderExpr(body, 0)}",
        parentPrec > 0,
      )

    case ESLam(_, _) =>
      val (base, stages) = collectStageLambdas(expr)
      maybeParens(
        s"sfun[${stages.mkString(", ")}] => ${renderExpr(base, 0)}",
        parentPrec > 0,
      )

    case ESApp(_, _) =>
      val (base, stages) = collectStageApps(expr)
      maybeParens(
        s"${renderExpr(base, 8)}[${stages.map(renderStage).mkString(", ")}]",
        parentPrec > 8,
      )

    case ELift(lam @ ELam(_, _, _, _), st) if st != Sta =>
      renderLiftedFun(lam, st, parentPrec)

    case ELift(e, st) =>
      maybeParens(
        s"lift[${renderStage(st)}](${renderExpr(e, 0)})",
        parentPrec > 7,
      )

    case ERun(t) =>
      maybeParens(s"run(${renderExpr(t, 0)})", parentPrec > 7)

    case EApp(e1, e2, st) =>
      val rendered = s"${renderExpr(e1, 8)}(${renderExpr(e2, 0)})${renderStageValue(st)}"
      maybeParens(rendered, parentPrec > 7)

    case ECBNApp(e1, e2) =>
      val rendered = s"${renderExpr(e1, 8)}(${renderExpr(e2, 0)})"
      maybeParens(rendered, parentPrec > 7)

    case EAssign(e1, e2, st) =>
      maybeParens(
        s"${renderExpr(e1, 1)} :=${renderStageValue(st)} ${renderExpr(e2, 1)}",
        parentPrec > 1,
      )

    case EBinOp(op, e1, e2, st) =>
      val prec = opPrecedence(op)
      maybeParens(
        s"${renderExpr(e1, prec)} ${renderOp(op, st)} ${renderExpr(e2, prec + 1)}",
        parentPrec > prec,
      )

    case EUnaryOp(op, e, st) =>
      maybeParens(s"$op${renderStageValue(st)} ${renderExpr(e, 6)}", parentPrec > 6)

    case EAlloc(e, st) =>
      maybeParens(s"ref${renderStageValue(st)}(${renderExpr(e, 0)})", parentPrec > 7)

    case EDeref(e, st) =>
      maybeParens(s"!${renderStageValue(st)} ${renderExpr(e, 6)}", parentPrec > 6)

    case EAscribe(e, asTy) =>
      maybeParens(s"${renderExpr(e, 0)} : ${renderType(asTy, 0)}", true)

    case EFix(f, e, st) =>
      maybeParens(s"fix${renderStageValue(st)} $f. ${renderExpr(e, 0)}", parentPrec > 0)

    case EIsApp(e) =>
      s"isApp(${renderExpr(e, 0)})"

    case EUnit => "()"
    case ENum(i) => i.toString
    case EBool(true) => "true"
    case EBool(false) => "false"
    case EVar(name) => name
    case ELoc(l) => s"loc($l)"

private def renderType(ty: Type, parentPrec: Int): String =
  ty match
    case TUnit => "Unit"
    case TInt => "Int"
    case TBool => "Bool"
    case TRef(t) => s"Ref[${renderType(t, 0)}]"
    case TCode(t) => s"Code[${renderType(t, 0)}]"
    case TForallSt(s, t) =>
      maybeParens(s"forall[$s]. ${renderType(t, 0)}", parentPrec > 0)
    case TFun(t1, t2) =>
      maybeParens(s"${renderType(t1, 1)} -> ${renderType(t2, 0)}", parentPrec > 0)
    case TAt(t, s) =>
      maybeParens(s"${renderType(t, 2)} @ ${renderStage(s)}", parentPrec > 1)

private def renderStage(stage: Stage): String =
  stage match
    case SNum(n) => n.toString
    case SVar(x) => x

private def renderStageValue(stage: Option[Stage]): String =
  stage match
    case Some(st) => s"@${renderStage(st)}"
    case None => ""

private def renderOp(op: String, stage: Option[Stage]): String =
  s"$op${renderStageValue(stage)}"

private def renderReturn(retTy: Option[Type]): String =
  retTy match
    case Some(ty) => s": ${renderType(ty, 0)}"
    case None => ""

private def renderLiftedFun(lam: ELam, stage: Stage, parentPrec: Int): String =
  val arg = lam.argTy.map(renderType(_, 0)).getOrElse("_")
  maybeParens(
    s"fun@${renderStage(stage)}(${lam.x}: $arg)${renderReturn(lam.retTy)} => ${renderExpr(lam.body, 0)}",
    parentPrec > 0,
  )

private def maybeParens(s: String, needParens: Boolean): String =
  if needParens then s"($s)" else s

private def opPrecedence(op: String): Int =
  op match
    case "*" | "/" => 5
    case "+" | "-" => 4
    case "<=" | ">=" | "<" | ">" | "==" | "!=" => 3
    case _ => 3

private def extractHeader(expr: Expr): Option[(List[HeaderBinder], Option[Type], Expr)] =
  val stripped =
    expr match
      case EAscribe(e, _) => e
      case other => other

  val binders = ArrayBuffer.empty[HeaderBinder]
  var current = stripped
  var retTy: Option[Type] = None
  var keepGoing = true

  while keepGoing do
    current match
      case ESLam(s, body) =>
        binders += HeaderBinder.Stage(s)
        current = body
      case ELam(x, argTy, body, lamRetTy) =>
        binders += HeaderBinder.Term(x, argTy)
        retTy = retTy.orElse(lamRetTy)
        current = body
      case _ =>
        keepGoing = false

  if binders.nonEmpty then Some((binders.toList, retTy, current))
  else None

private def renderHeader(binders: List[HeaderBinder]): String =
  val out = new StringBuilder
  var rest = binders

  while rest.nonEmpty do
    rest match
      case HeaderBinder.Stage(_) :: _ =>
        val stages = ArrayBuffer.empty[String]
        while rest.nonEmpty && rest.head.isInstanceOf[HeaderBinder.Stage] do
          rest.head match
            case HeaderBinder.Stage(name) => stages += name
            case _ => ()
          rest = rest.tail
        out.append(s"[${stages.mkString(", ")}]")
      case HeaderBinder.Term(name, Some(ty)) :: tail =>
        out.append(s" ($name: ${renderType(ty, 0)})")
        rest = tail
      case HeaderBinder.Term(name, None) :: tail =>
        out.append(s" ($name)")
        rest = tail

  out.result()

private def collectStageLambdas(expr: Expr): (Expr, List[String]) =
  val stages = ArrayBuffer.empty[String]
  var current = expr
  var keepGoing = true
  while keepGoing do
    current match
      case ESLam(s, body) =>
        stages += s
        current = body
      case _ =>
        keepGoing = false
  (current, stages.toList)

private def collectStageApps(expr: Expr): (Expr, List[Stage]) =
  val stages = ArrayBuffer.empty[Stage]
  var current = expr
  var keepGoing = true
  while keepGoing do
    current match
      case ESApp(e, st) =>
        stages.prepend(st)
        current = e
      case _ =>
        keepGoing = false
  (current, stages.toList)
