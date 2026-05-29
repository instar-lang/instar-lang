package instar.syntax

enum Stage:
  case Sta, Dyn

type Loc = Int

enum Expr:
  case EUnit
  case ENum(i: Int)
  case EBool(b: Boolean)
  case EVar(name: String)
  case ELam(x: String, body: Expr)
  case EBNLam(x: String, body: Expr)
  case EApp(e1: Expr, e2: Expr, st: Stage)
  case ELift(t: Expr)
  case ERun(t: Expr)
  case ELet(x: String, rhs: Expr, body: Expr)
  case ELetRec(f: String, rhs: Expr, body: Expr)
  case ECond(e1: Expr, e2: Expr, e3: Expr, st: Stage)
  case EBinOp(op: String, e1: Expr, e2: Expr, st: Stage)
  case EUnaryOp(op: String, e: Expr, st: Stage)
  case EAlloc(e: Expr, st: Stage)
  case EDeref(e: Expr, st: Stage)
  case EAssign(e1: Expr, e2: Expr, st: Stage)
  case EFix(f: String, e: Expr, st: Stage)
  case ELoc(l: Loc)
  case EIsApp(e: Expr)
  case ECBNApp(e1: Expr, e2: Expr)

enum Value:
  case VUnit
  case VNum(i: Int)
  case VBool(b: Boolean)
  case VLoc(loc: Loc)
  case VClo(x: String, body: Expr, ρ: Env)
  case VBNClo(x: String, body: Expr, ρ: Env)
  case VCode(t: Expr)
  case VThunk(e: Expr, ρ: Env)

type Env = Map[String, Loc]

extension (e: Expr)
  def isPure: Boolean =
    e match
      case EUnit | ENum(_) | EBool(_) | EVar(_) => true
      case ELam(_, _) | EBNLam(_, _) => true
      case EBinOp(_, _, _, _) | EUnaryOp(_, _, _) => true
      case EApp(_, _, _) => false
      case ELift(_) => false
      case EAlloc(_, _) | EDeref(_, _) | EAssign(_, _, _) => false
      case ERun(t) => t.isPure
      case ELet(_, rhs, body) => rhs.isPure && body.isPure
      case ELetRec(_, rhs, body) => rhs.isPure && body.isPure
      case ECond(e1, e2, e3, _) => e1.isPure && e2.isPure && e3.isPure
      case EFix(_, e, _) => e.isPure
      case _ => false

  def freeVar: Set[String] =
    e match
      case EUnit | ENum(_) | EBool(_) => Set()
      case EVar(x) => Set(x)
      case ELam(x, body) => body.freeVar - x
      case EBNLam(x, body) => body.freeVar - x
      case EApp(e1, e2, _) => e1.freeVar ++ e2.freeVar
      case ECBNApp(e1, e2) => e1.freeVar ++ e2.freeVar
      case ELift(t) => t.freeVar
      case ERun(t) => t.freeVar
      case ELet(x, rhs, body) => rhs.freeVar ++ (body.freeVar - x)
      case ELetRec(f, rhs, body) => (rhs.freeVar - f) ++ (body.freeVar - f)
      case ECond(e1, e2, e3, _) => e1.freeVar ++ e2.freeVar ++ e3.freeVar
      case EBinOp(_, e1, e2, _) => e1.freeVar ++ e2.freeVar
      case EUnaryOp(_, e, _) => e.freeVar
      case EAlloc(e, _) => e.freeVar
      case EDeref(e, _) => e.freeVar
      case EAssign(e1, e2, _) => e1.freeVar ++ e2.freeVar
      case EFix(f, e, _) => e.freeVar - f

  def subst(from: String, to: Expr): Expr =
    e match
      case EUnit | ENum(_) | EBool(_) => e
      case EVar(x) => if x == from then to else e
      case ELam(x, body) => ELam(x, body.subst(from, to))
      case EBNLam(x, body) => EBNLam(x, body.subst(from, to))
      case EApp(e1, e2, st) => EApp(e1.subst(from, to), e2.subst(from, to), st)
      case ECBNApp(e1, e2) => ECBNApp(e1.subst(from, to), e2.subst(from, to))
      case ELift(t) => ELift(t.subst(from, to))
      case ERun(t) => ERun(t.subst(from, to))
      case ELet(x, rhs, body) =>
        ELet(x, rhs.subst(from, to), body.subst(from, to))
      case ELetRec(f, rhs, body) =>
        ELetRec(f, rhs.subst(from, to), body.subst(from, to))
      case ECond(e1, e2, e3, s) =>
        ECond(e1.subst(from, to), e2.subst(from, to), e3.subst(from, to), s)
      case EBinOp(op, e1, e2, s) => EBinOp(op, e1.subst(from, to), e2.subst(from, to), s)
      case EUnaryOp(op, e, s) => EUnaryOp(op, e.subst(from, to), s)
      case EAlloc(e, s) => EAlloc(e.subst(from, to), s)
      case EDeref(e, s) => EDeref(e.subst(from, to), s)
      case EAssign(e1, e2, s) => EAssign(e1.subst(from, to), e2.subst(from, to), s)
      case EFix(f, e, s) => EFix(f, e.subst(from, to), s)
      case EIsApp(e) => EIsApp(e.subst(from, to))

import Stage.*
import Expr.*
import Value.*

def ENum1(i: Int): Expr = ENum(i)
def ENum2(i: Int): Expr = ELift(ENum(i))
def EBool1(b: Boolean): Expr = EBool(b)
def EBool2(b: Boolean): Expr = ELift(EBool(b))
def EApp1(e1: Expr, e2: Expr): Expr = EApp(e1, e2, Sta)
def EApp2(e1: Expr, e2: Expr): Expr = EApp(e1, e2, Dyn)
def ECond1(e1: Expr, e2: Expr, e3: Expr): Expr = ECond(e1, e2, e3, Sta)
def ECond2(e1: Expr, e2: Expr, e3: Expr): Expr = ECond(e1, e2, e3, Dyn)
def EBinOp1(op: String, e1: Expr, e2: Expr): Expr = EBinOp(op, e1, e2, Sta)
def EBinOp2(op: String, e1: Expr, e2: Expr): Expr = EBinOp(op, e1, e2, Dyn)
def EUnaryOp1(op: String, e: Expr): Expr = EUnaryOp(op, e, Sta)
def EUnaryOp2(op: String, e: Expr): Expr = EUnaryOp(op, e, Dyn)
def EAlloc1(e: Expr): Expr = EAlloc(e, Sta)
def EAlloc2(e: Expr): Expr = EAlloc(e, Dyn)
def EDeref1(e: Expr): Expr = EDeref(e, Sta)
def EDeref2(e: Expr): Expr = EDeref(e, Dyn)
def EAssign1(e1: Expr, e2: Expr): Expr = EAssign(e1, e2, Sta)
def EAssign2(e1: Expr, e2: Expr): Expr = EAssign(e1, e2, Dyn)

def show(e: Expr): String = pprint(e, 0)

private def line(e: Expr, d: Int): String = s"${"  " * d}${pprint(e, d)}"

def pprint(e: Expr, d: Int): String =
  val I = "  " * d
  e match
    case EUnit => "()"
    case ENum(i) => i.toString
    case EBool(b) => b.toString
    case EVar(x) => x
    case ELam(x, b) => s"λ$x.\n${line(b, d + 1)}"
    case EBNLam(x, b) => s"λb$x.\n${line(b, d + 1)}"
    case EApp(e1, e2, Sta) => s"(${show(e1)} ${show(e2)})"
    case EApp(e1, e2, Dyn) => s"(${show(e1)} @² ${show(e2)})"
    case ELift(t) => s"lift(${show(t)})"
    case ERun(t) => s"run(${show(t)})"
    case ELet(x, r, b) => s"let $x = ${pprint(r, d)} in\n${line(b, d)}"
    case ELetRec(f, r, b) => s"letrec $f = ${pprint(r, d)} in\n${line(b, d + 1)}"
    case ECond(e1, e2, e3, Sta) =>
      s"if ${show(e1)}\n${I}then\n${line(e2, d + 1)}\n${I}else\n${line(e3, d + 1)}"
    case ECond(e1, e2, e3, Dyn) =>
      s"if² ${show(e1)}\n${I}then\n${line(e2, d + 1)}\n${I}else\n${line(e3, d + 1)}"
    case EBinOp(op, e1, e2, Sta) => s"(${pprint(e1, 0)} $op ${pprint(e2, 0)})"
    case EBinOp(op, e1, e2, Dyn) => s"(${pprint(e1, 0)} $op² ${pprint(e2, 0)})"
    case EUnaryOp(op, e, Sta) => s"($op ${pprint(e, 0)})"
    case EUnaryOp(op, e, Dyn) => s"($op² ${pprint(e, 0)})"
    case EAlloc(e, Sta) => s"ref ${pprint(e, 0)}"
    case EAlloc(e, Dyn) => s"ref² ${pprint(e, 0)}"
    case EDeref(e, Sta) => s"!${pprint(e, 0)}"
    case EDeref(e, Dyn) => s"!²${pprint(e, 0)}"
    case EAssign(e1, e2, Sta) => s"(${pprint(e1, 0)} := ${pprint(e2, 0)})"
    case EAssign(e1, e2, Dyn) => s"(${pprint(e1, 0)} :=² ${pprint(e2, 0)})"
    case EFix(f, e, Sta) => s"fix $f. ${pprint(e, 0)}"
    case EFix(f, e, Dyn) => s"fix² $f. ${pprint(e, 0)}"
    case ELoc(l) => s"<loc: $l>"
    case EIsApp(e) => s"isApp(${pprint(e, 0)})"
    case ECBNApp(e1, e2) => s"(${pprint(e1, 0)} @@ ${pprint(e2, 0)})"

def show(v: Value): String = v match
  case VCode(e) => s"⟨code:\n${line(e, 1)}⟩"
  case VClo(x, b, _) => s"⟨closure: λ$x.\n${line(b, 1)}⟩"
  case VBNClo(x, b, _) => s"⟨by-name closure: λ$x.\n${line(b, 1)}⟩"
  case VNum(i) => i.toString
  case VBool(b) => b.toString
  case VUnit => "()"
  case VLoc(l) => s"<loc: $l>"
  case VThunk(e, _) => s"⟨thunk: ${pprint(e, 0)}⟩"