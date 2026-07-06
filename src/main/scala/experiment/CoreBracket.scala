package instar.experiment.corebracket

// The core language:
// - After inference and elaboration phases, assuming programs are now well-typed.
// - All stage information is made explicit in the AST.
// - Lambda terms could carry type annotations for their argument and return types.
// - `Stage` annotates can be either a stage index/number or a stage variable.
//   Stage variables are introduced by `ESLam` e.g. Λs. app(t1, t2, s).

import instar.Counter.*
import PreExpr.*

// I guess
// https://stackoverflow.com/questions/38243530/custom-exception-in-scala/43942163#43942163
class TranslationException(message: String) extends Exception(message) {

  def this(message: String, cause: Throwable) = {
    this(message)
    initCause(cause)
  }

  def this(cause: Throwable) = {
    this(Option(cause).map(_.toString).orNull, cause)
  }

  def this() = {
    this(null: String)
  }
}

enum Stage:
  case SNum(n: Int)
  case SVar(x: String)

val Sta: Stage.SNum = Stage.SNum(0)
val Dyn: Stage.SNum = Stage.SNum(1)

enum Type:
  case TUnit, TInt, TBool
  case TFun(t1: Type, t2: Type)
  case TForallSt(s: String, t: Type)
  case TAt(t: Type, s: Stage)
  case TCode(t: Type)

enum Expr:
  var ty: Option[Type] = None
  def withType(t: Type): Expr = { ty = Some(t); this }
  case EUnit
  case ENum(i: Int)
  case EBool(b: Boolean)
  case EVar(name: String)
  case ESLam(x: String, body: Expr)
  case ESApp(e: Expr, st: Stage)
  case ELam(x: String, argTy: Option[Type], body: Expr, retTy: Option[Type])
  case EApp(e1: Expr, e2: Expr, st: Stage)
  case ELift(t: Expr, to: Stage)
  case ERun(t: Expr)
  case ELet(x: String, rhs: Expr, body: Expr)
  case ECond(e1: Expr, e2: Expr, e3: Expr, st: Stage)
  case EBinOp(op: String, e1: Expr, e2: Expr, st: Stage)
  case EUnaryOp(op: String, e: Expr, st: Stage)
  case EAscribe(e: Expr, asTy: Type)

enum PreExpr:
  var ty: Option[Type] = None
  def withType(t: Type): PreExpr = { ty = Some(t); this }
  case PUnit
  case PNum(i: Int)
  case PBool(b: Boolean)
  case PVar(name: String)
  case PSLam(x: String, body: PreExpr)
  case PSApp(e: PreExpr, st: Stage)
  case PLam(x: String, argTy: Option[Type], body: PreExpr, retTy: Option[Type])
  case PApp(e1: PreExpr, e2: PreExpr, st: Stage)
  case PLift(t: PreExpr, to: Stage)
  case PRun(t: PreExpr)
  case PLet(x: String, rhs: PreExpr, body: PreExpr)
  case PCond(e1: PreExpr, e2: PreExpr, e3: PreExpr, st: Stage)
  case PBinOp(op: String, e1: PreExpr, e2: PreExpr, st: Stage)
  case PUnaryOp(op: String, e: PreExpr, st: Stage)
  case PAscribe(e: PreExpr, asTy: Type)
  case PBracket(e: PreExpr)
  case PEscape(e: PreExpr)

def PApp1(e1: PreExpr, e2: PreExpr): PreExpr = PApp(e1, e2, Sta)
def PApp2(e1: PreExpr, e2: PreExpr): PreExpr = PApp(e1, e2, Dyn)
def PLift1(t: PreExpr): PreExpr = PLift(t, Sta)
def PLift2(t: PreExpr): PreExpr = PLift(t, Dyn)
def PCond1(e1: PreExpr, e2: PreExpr, e3: PreExpr): PreExpr = PCond(e1, e2, e3, Sta)
def PCond2(e1: PreExpr, e2: PreExpr, e3: PreExpr): PreExpr = PCond(e1, e2, e3, Dyn)
def PBinOp1(op: String, e1: PreExpr, e2: PreExpr): PreExpr = PBinOp(op, e1, e2, Sta)
def PBinOp2(op: String, e1: PreExpr, e2: PreExpr): PreExpr = PBinOp(op, e1, e2, Dyn)
def PUnaryOp1(op: String, e: PreExpr): PreExpr = PUnaryOp(op, e, Sta)
def PUnaryOp2(op: String, e: PreExpr): PreExpr = PUnaryOp(op, e, Dyn)

def translate(pe: PreExpr): Expr = transUnb(pe, Map(), true)


// regular vars to the stages they're from
type StAnnotEnv = Map[String, Stage.SNum]

// translation of the contents of non-bracketed code: id except for brackets & escapes
def transUnb(pe: PreExpr, annenv: StAnnotEnv, toplvl: Boolean): Expr =
  pe match
    case PUnit => EUnit
    case PNum(i) => ENum(i)
    case PBool(b) => EBool(b)
    case PVar(name) => { annenv.get(name) match
                        case Some(Sta) => EVar(name)
                        case Some(Dyn) => throw new TranslationException("A variable that was bound within brackets is used outside brackets")
                        case _         => throw new TranslationException("Variable not found in environment") }
    case PSLam(x, body) => ESLam(x, transUnb(body, annenv, toplvl))
    case PSApp(e, st) => ESApp(transUnb(e, annenv, toplvl), st)
    case PLam(x, argTy, body, retTy) => ELam(x, argTy, transUnb(body, annenv + (x -> Sta), toplvl), retTy)
    case PApp(e1, e2, st) => EApp(transUnb(e1, annenv, toplvl), transUnb(e2, annenv, toplvl), st)
    case PLift(t, to) => ELift(transUnb(t, annenv, toplvl), to)
    case PRun(t) => ERun(transUnb(t, annenv, toplvl))
    case PLet(x, rhs, body) => ELet(x, transUnb(rhs, annenv, toplvl), transUnb(body, annenv + (x -> Sta), toplvl)) // TODO?
    case PCond(e1, e2, e3, st) => ECond(transUnb(e1, annenv, toplvl), transUnb(e2, annenv, toplvl), transUnb(e3, annenv, toplvl), st)
    case PBinOp(op, e1, e2, st) => EBinOp(op, transUnb(e1, annenv, toplvl), transUnb(e2, annenv, toplvl), st)
    case PUnaryOp(op, e, st) => EUnaryOp(op, transUnb(e, annenv, toplvl), st)
    case PAscribe(e, asTy) => EAscribe(transUnb(e, annenv, toplvl), asTy)
    case PBracket(e) => transBra(e, annenv) // TODO?
    case PEscape(e) => if toplvl
                       then throw new TranslationException("Escape is not allowed in unquoted code")
                       else transUnb(e, annenv, toplvl)


def mka(f: Expr, x: Expr): Expr = EApp(f, x, Dyn)
def mkl(x: String, t1: Option[Type], e: Expr, t2: Option[Type]): Expr = ELift2(ELam(x, t1, e, t2))
def isCodeType(t: Option[Type]): Boolean =
  t match
    case Some(Type.TCode(_)) => true
    case _ => false


// translation of the contents of brackets
def transBra(pe: PreExpr, aenv: StAnnotEnv): Expr =
  pe match
    case PUnit      => ELift2(EUnit)
    case PNum(i)    => ELift2(ENum(i))
    case PBool(b)   => ELift2(EBool(b))
    case PVar(name) => { aenv.get(name) match // no initial env, so no use of mkid combinator
                         case Some(Sta) => ELift2(EVar(name))
                         case Some(Dyn) => EVar(name)
                         case _         => throw new TranslationException("Variable not found in environment") }
    case PSLam(x, body)   => throw new TranslationException("Stage-polymorphic lambdas are not allowed to be formed in brackets")
    case PSApp(e, st)     => throw new TranslationException("Stage-polymorphic function application cannot be formed in brackets, use escape instead")
    case PLam(x, argTy, body, retTy) => mkl(x, argTy, transBra(body, aenv + (x -> Dyn)), retTy)
    case PApp(e1, e2, st) => if st == Sta
                              then mka(transBra(e1, aenv), transBra(e2, aenv))
                              else throw new TranslationException("Application to future stage is ")
    case PLift(t, to)     => if to == Sta // "lift" can only appear in brackets when it is to Sta
                             then ELift1(transBra(t, aenv))
                             else throw new TranslationException("Lift to future stage is not allowed in brackets")
    case PRun(t)          => throw new TranslationException("Run is not allowed in brackets")
    //TODO: is this right?
    case PLet(x, rhs, body)     => ELet(x, transBra(rhs, aenv), transBra(body, aenv + (x -> Dyn)))
    // Stage polymorphism in brackets degenerates to be monomorphically Dyn
    // thus PSApp translates successfully in brackets only when stage == Sta
    case PCond(e1, e2, e3, st)  => if st == Sta
                                   then ECond2(transBra(e1, aenv), transBra(e2, aenv), transBra(e3, aenv))
                                   else throw new TranslationException("Conditional to future stage is not allowed in brackets")
    case PBinOp(op, e1, e2, st) => if st == Sta
                                   then EBinOp2(op, transBra(e1, aenv), transBra(e2, aenv))
                                   else throw new TranslationException("Binary operation to future stage is not allowed in brackets")
    case PUnaryOp(op, e, st)    => if st == Sta
                                   then EUnaryOp2(op, transBra(e, aenv))
                                   else throw new TranslationException("Unary operation to future stage is not allowed in brackets")
    case PAscribe(e, asTy) => ELift2(EAscribe(transBra(e, aenv), asTy)) // TODO?
    case PBracket(e)       => throw new TranslationException("No nested brackets allowed")
    case PEscape(e)        => if isCodeType(e.ty) // TODO: this guard should be elsewhere
                              then transUnb(e, aenv, false)
                              else throw new TranslationException("Cannot escape term of non-code type")




def EApp1(e1: Expr, e2: Expr): Expr = EApp(e1, e2, Sta)
def EApp2(e1: Expr, e2: Expr): Expr = EApp(e1, e2, Dyn)
def ECond1(e1: Expr, e2: Expr, e3: Expr): Expr = ECond(e1, e2, e3, Sta)
def ECond2(e1: Expr, e2: Expr, e3: Expr): Expr = ECond(e1, e2, e3, Dyn)
def EBinOp1(op: String, e1: Expr, e2: Expr): Expr = EBinOp(op, e1, e2, Sta)
def EBinOp2(op: String, e1: Expr, e2: Expr): Expr = EBinOp(op, e1, e2, Dyn)
def EUnaryOp1(op: String, e: Expr): Expr = EUnaryOp(op, e, Sta)
def EUnaryOp2(op: String, e: Expr): Expr = EUnaryOp(op, e, Dyn)

// Note: they lift term to stage 1/2, but lift itself can only be at stage 1
def ELift1(e: Expr): Expr = ELift(e, Sta)
def ELift2(e: Expr): Expr = ELift(e, Dyn)

enum Value:
  case VUnit
  case VNum(i: Int)
  case VBool(b: Boolean)
  case VSClo(st: String, body: Expr, ρ: Env, ς: StEnv)
  case VClo(x: String, argTy: Option[Type], body: Expr, retTy: Option[Type], ρ: Env, ς: StEnv)
  case VCode(e: Expr) // XXX: could extend to open code value with environment?

extension (t: Option[Type])
  // Assuming well-formedness of types
  def erase: Option[Type] =
    t match
      case Some(TCode(t1)) => Some(t1)
      case _ => t

import Stage.*
import Expr.*
import Type.*
import Value.*

type Env = Map[String, Value]
type StEnv = Map[String, Stage]
type Ans = Value

type Cont = (Value, MCont) => Value
type MCont = Value => Value

def reflect(e: Expr, k: Cont, γ: MCont): Value =
  e match
    // Note: here we decide what needs to be let-inserted based on syntactic form.
    // We could also avoid let-inserting for λ-terms and fix as they are pure.
    case EUnit | ENum(_) | EBool(_) => k(VCode(e), γ)
    case _ =>
      val x = fresh()
      // In reduction semantics, we have the let-insertion rule
      // P[E[reflect t]] -> P[let x = t in E[x]].
      // Here, the continuation k is the E context, and γ is the P context.
      k(VCode(EVar(x)), { case VCode(t) =>
        γ(VCode(ELet(x, e, t)))
      })

def reify(e: Expr, ρ: Env, ς: StEnv, γ: MCont): Value =
  eval(e, ρ, ς, (x, γ1) => γ1(x), γ)

def lift(k: Cont)(v: Value, γ: MCont): Value =
  v match
    case VUnit => reflect(EUnit, k, γ)
    case VNum(i) => reflect(ENum(i), k, γ)
    case VBool(b) => reflect(EBool(b), k, γ)
    case VClo(x, argTy, body, retTy, ρf, ςf) =>
      val y = fresh()
      reify(body, ρf + (x -> VCode(EVar(y))), ςf, { case VCode(t) =>
        reflect(ELam(y, argTy.erase, t, retTy.erase), k, γ)
      })

def evalPrim(op: String, v1: Value, v2: Value): Value =
  (op, v1, v2) match
    case ("+", VNum(i1), VNum(i2)) => VNum(i1 + i2)
    case ("-", VNum(i1), VNum(i2)) => VNum(i1 - i2)
    case ("*", VNum(i1), VNum(i2)) => VNum(i1 * i2)
    case ("/", VNum(i1), VNum(i2)) => VNum(i1 / i2)
    case ("<=", VNum(i1), VNum(i2)) => VBool(i1 <= i2)
    case (">=", VNum(i1), VNum(i2)) => VBool(i1 >= i2)
    case ("<", VNum(i1), VNum(i2)) => VBool(i1 < i2)
    case (">", VNum(i1), VNum(i2)) => VBool(i1 > i2)
    case ("==", VNum(i1), VNum(i2)) => VBool(i1 == i2)
    case ("!=", VNum(i1), VNum(i2)) => VBool(i1 != i2)

def evalPrimUnary(op: String, v: Value): Value =
  (op, v) match
    case ("-", VNum(i)) => VNum(-i)

def evalStVar(s: Stage, ς: StEnv): Stage =
  s match
    case SVar(st) => ς(st)
    case _ => s

def eval(e: Expr, ρ: Env, ς: StEnv, k: Cont, γ: MCont): Value =
  e match
    case EUnit =>
      k(VUnit, γ)
    case ENum(i) =>
      k(VNum(i), γ)
    case EBool(b) =>
      k(VBool(b), γ)
    case EVar(x) =>
      k(ρ(x), γ)
    case ESLam(x, body) =>
      k(VSClo(x, body, ρ, ς), γ)
    case ESApp(e, st) =>
      eval(e, ρ, ς, { case (VSClo(x, body, ρf, ςf), γ1) =>
        eval(body, ρf, ςf + (x -> evalStVar(st, ς)), k, γ1)
      }, γ)
    case ELam(x, argTy, e, retTy) =>
      k(VClo(x, argTy, e, retTy, ρ, ς), γ)
    case EApp(e1, e2, s) if evalStVar(s, ς) == Sta =>
      eval(e1, ρ, ς, { case (VClo(x, _, body, _, ρf, ςf), γ1) =>
        eval(e2, ρ, ς, (v2, γ2) =>
          eval(body, ρf + (x -> v2), ςf, k, γ2), γ1)
      }, γ)
    case EApp(e1, e2, s) if evalStVar(s, ς) == Dyn =>
      eval(e1, ρ, ς, { case (VCode(x1), γ1) =>
        eval(e2, ρ, ς, { case (VCode(x2), γ2) =>
          reflect(EApp1(x1, x2), k, γ2)
        }, γ1)
      }, γ)
    case ELift(e, to) if evalStVar(to, ς) == Sta =>
      eval(e, ρ, ς, k, γ)
    case ELift(e, to) if evalStVar(to, ς) == Dyn =>
      eval(e, ρ, ς, lift(k), γ)
    case ERun(e) =>
      // Note: Because `Run` is a R context, we need to reify first.
      // Here we assume that t is a closed expression without any
      // free variables, locations and stage variables.
      reify(e, ρ, ς, { case VCode(t) =>
        eval(t, Map(), Map(), k, γ)
      })
    case ELet(x, rhs, e) =>
      eval(rhs, ρ, ς, (v, γ1) => eval(e, ρ + (x -> v), ς, k, γ1), γ)
    case ECond(e1, e2, e3, s) if evalStVar(s, ς) == Sta =>
      eval(e1, ρ, ς, { case (VBool(b), γ1) =>
        if b then eval(e2, ρ, ς, k, γ1)
        else eval(e3, ρ, ς, k, γ1)
      }, γ)
    case ECond(e1, e2, e3, s) if evalStVar(s, ς) == Dyn =>
      eval(e1, ρ, ς, { case (VCode(x1), γ1) =>
        reify(e2, ρ, ς, { case VCode(x2) =>
          reify(e3, ρ, ς, { case VCode(x3) =>
            reflect(ECond1(x1, x2, x3), k, γ1)
          })
        })
      }, γ)
    case EBinOp(op, e1, e2, s) if evalStVar(s, ς) == Sta =>
      eval(e1, ρ, ς, { case (v1, γ1) =>
        eval(e2, ρ, ς, { case (v2, γ2) =>
          k(evalPrim(op, v1, v2), γ2)
        }, γ1)
      }, γ)
    case EBinOp(op, e1, e2, s) if evalStVar(s, ς) == Dyn =>
      eval(e1, ρ, ς, { case (VCode(x1), γ1) =>
        eval(e2, ρ, ς, { case (VCode(x2), γ2) =>
          reflect(EBinOp1(op, x1, x2), k, γ2)
        }, γ1)
      }, γ)
    case EUnaryOp(op, e, s) if evalStVar(s, ς) == Sta =>
      eval(e, ρ, ς, { case (v, γ1) =>
        k(evalPrimUnary(op, v), γ1)
      }, γ)
    case EUnaryOp(op, e, s) if evalStVar(s, ς) == Dyn =>
      eval(e, ρ, ς, { case (VCode(x), γ1) =>
        reflect(EUnaryOp1(op, x), k, γ1)
      }, γ)
    case EAscribe(e, _) => eval(e, ρ, ς, k, γ)

def eval(e: Expr): Ans =
  clear
  eval(e, Map(), Map(), (x, γ) => γ(x), x => x)

def eval(pe: PreExpr): Ans =
  clear
  eval(translate(pe), Map(), Map(), (x, γ) => γ(x), x => x)