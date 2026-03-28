package instar.parser

import scala.collection.mutable.ArrayBuffer

import instar.syntax.*
import Expr.*
import Stage.*
import Type.*

object Lexer:
  enum Kind:
    case Identifier
    case IntLit
    case LParen
    case RParen
    case LBracket
    case RBracket
    case Colon
    case At
    case Comma
    case Dot
    case Equal
    case Arrow
    case FatArrow
    case Plus
    case Minus
    case Star
    case Slash
    case LessEq
    case GreaterEq
    case Less
    case Greater
    case EqEq
    case Bang
    case BangEq
    case True
    case False
    case Fun
    case SFun
    case Lift
    case Let
    case In
    case LetRec
    case Fix
    case If
    case Then
    case Else
    case Ref
    case Assign
    case IsApp
    case Forall
    case Run
    case EOF

  case class Token(kind: Kind, lexeme: String, line: Int, col: Int)

  final class LexerException(message: String) extends RuntimeException(message)

  private val keywords: Map[String, Kind] = Map(
    "true" -> Kind.True,
    "false" -> Kind.False,
    "fun" -> Kind.Fun,
    "sfun" -> Kind.SFun,
    "lift" -> Kind.Lift,
    "let" -> Kind.Let,
    "in" -> Kind.In,
    "letrec" -> Kind.LetRec,
    "fix" -> Kind.Fix,
    "if" -> Kind.If,
    "then" -> Kind.Then,
    "else" -> Kind.Else,
    "ref" -> Kind.Ref,
    "isApp" -> Kind.IsApp,
    "forall" -> Kind.Forall,
    "run" -> Kind.Run,
  )

  def lex(input: String): Vector[Token] =
    val out = ArrayBuffer.empty[Token]
    var i = 0
    var line = 1
    var col = 1

    def current(offset: Int = 0): Char =
      input.charAt(i + offset)

    def atEnd(offset: Int = 0): Boolean =
      i + offset >= input.length

    def advance(): Char =
      val ch = input.charAt(i)
      i += 1
      if ch == '\n' then
        line += 1
        col = 1
      else
        col += 1
      ch

    def add(kind: Kind, lexeme: String, startLine: Int, startCol: Int): Unit =
      out += Token(kind, lexeme, startLine, startCol)

    def skipWhitespaceAndComments(): Unit =
      var keepGoing = true
      while keepGoing && !atEnd() do
        current() match
          case ch if ch.isWhitespace =>
            advance()
          case '/' if !atEnd(1) && current(1) == '/' =>
            while !atEnd() && current() != '\n' do advance()
          case '/' if !atEnd(1) && current(1) == '*' =>
            advance()
            advance()
            var closed = false
            while !atEnd() && !closed do
              if current() == '*' && !atEnd(1) && current(1) == '/' then
                advance()
                advance()
                closed = true
              else
                advance()
            if !closed then
              throw LexerException(s"Unterminated block comment at $line:$col")
          case _ =>
            keepGoing = false

    while
      skipWhitespaceAndComments()
      !atEnd()
    do
      val startLine = line
      val startCol = col
      current() match
        case ch if ch.isLetter || ch == '_' =>
          val sb = new StringBuilder
          while !atEnd() && (current().isLetterOrDigit || current() == '_') do
            sb += advance()
          val lexeme = sb.result()
          add(keywords.getOrElse(lexeme, Kind.Identifier), lexeme, startLine, startCol)

        case ch if ch.isDigit =>
          val sb = new StringBuilder
          while !atEnd() && current().isDigit do sb += advance()
          add(Kind.IntLit, sb.result(), startLine, startCol)

        case '(' => advance(); add(Kind.LParen, "(", startLine, startCol)
        case ')' => advance(); add(Kind.RParen, ")", startLine, startCol)
        case '[' => advance(); add(Kind.LBracket, "[", startLine, startCol)
        case ']' => advance(); add(Kind.RBracket, "]", startLine, startCol)
        case ':' =>
          advance()
          if !atEnd() && current() == '=' then
            advance()
            add(Kind.Assign, ":=", startLine, startCol)
          else
            add(Kind.Colon, ":", startLine, startCol)
        case '@' => advance(); add(Kind.At, "@", startLine, startCol)
        case ',' => advance(); add(Kind.Comma, ",", startLine, startCol)
        case '.' => advance(); add(Kind.Dot, ".", startLine, startCol)
        case '+' => advance(); add(Kind.Plus, "+", startLine, startCol)
        case '*' => advance(); add(Kind.Star, "*", startLine, startCol)
        case '/' => advance(); add(Kind.Slash, "/", startLine, startCol)
        case '-' =>
          advance()
          if !atEnd() && current() == '>' then
            advance()
            add(Kind.Arrow, "->", startLine, startCol)
          else
            add(Kind.Minus, "-", startLine, startCol)
        case '=' =>
          advance()
          if !atEnd() && current() == '>' then
            advance()
            add(Kind.FatArrow, "=>", startLine, startCol)
          else if !atEnd() && current() == '=' then
            advance()
            add(Kind.EqEq, "==", startLine, startCol)
          else
            add(Kind.Equal, "=", startLine, startCol)
        case '!' =>
          advance()
          if !atEnd() && current() == '=' then
            advance()
            add(Kind.BangEq, "!=", startLine, startCol)
          else
            add(Kind.Bang, "!", startLine, startCol)
        case '<' =>
          advance()
          if !atEnd() && current() == '=' then
            advance()
            add(Kind.LessEq, "<=", startLine, startCol)
          else
            add(Kind.Less, "<", startLine, startCol)
        case '>' =>
          advance()
          if !atEnd() && current() == '=' then
            advance()
            add(Kind.GreaterEq, ">=", startLine, startCol)
          else
            add(Kind.Greater, ">", startLine, startCol)
        case other =>
          throw LexerException(s"Unexpected character $other at $startLine:$startCol")

    out += Token(Kind.EOF, "", line, col)
    out.toVector

import Lexer.Kind
import Lexer.Token

final class ParserException(message: String) extends RuntimeException(message)

def lex(input: String): Vector[Token] =
  Lexer.lex(input)

def parse(input: String): Expr =
  Parser(lex(input)).parseProgram()

def parseType(input: String): Type =
  Parser(lex(input)).parseStandaloneType()

private case class Parser(tokens: Vector[Token]):
  private enum HeaderBinder:
    case Stage(name: String)
    case Term(name: String, ty: Type)

  private var pos = 0

  private def current: Token = tokens(pos)
  private def peek(offset: Int): Token = tokens(math.min(pos + offset, tokens.length - 1))
  private def at(kind: Kind): Boolean = current.kind == kind
  private def advance(): Token =
    val tok = current
    if pos < tokens.length - 1 then pos += 1
    tok

  private def expect(kind: Kind, expected: String): Token =
    if at(kind) then advance()
    else fail(s"Expected $expected but found `${current.lexeme}`")

  private def fail(message: String): Nothing =
    throw ParserException(s"$message at ${current.line}:${current.col}")

  def parseProgram(): Expr =
    val expr = parseExpr()
    expect(Kind.EOF, "end of input")
    expr

  def parseStandaloneType(): Type =
    val ty = parseTypeExpr()
    expect(Kind.EOF, "end of input")
    ty

  private def parseExpr(): Expr =
    current.kind match
      case Kind.Let => parseLet()
      case Kind.LetRec => parseLetRec()
      case Kind.Fun => parseFun()
      case Kind.SFun => parseSFun()
      case Kind.Fix => parseFix()
      case Kind.If => parseIf()
      case _ => parseAssignment()

  private def parseAssignment(): Expr =
    val lhs = parseComparison()
    if at(Kind.Assign) then
      advance()
      val stage = parseOptionalStageValue()
      val rhs = parseAssignment()
      EAssign(lhs, rhs, stage)
    else
      lhs

  private def parseLet(): Expr =
    expect(Kind.Let, "`let`")
    val name = parseIdentifier("binding name")
    val binders = parseHeaderBinders()

    if binders.nonEmpty then
      val retTy = parseOptionalTypeAnnotation()
      expect(Kind.Equal, "`=`")
      val rhsBody = parseExpr()
      expect(Kind.In, "`in`")
      val body = parseExpr()

      val rhs = buildHeaderRhs(binders, retTy, rhsBody)
      val rhsWithAnn =
        retTy match
          case Some(ty) => EAscribe(rhs, buildHeaderType(binders, ty))
          case None => rhs
      ELet(name, rhsWithAnn, body)
    else
      val ann = parseOptionalTypeAnnotation()
      expect(Kind.Equal, "`=`")
      val rhs = parseExpr()
      expect(Kind.In, "`in`")
      val body = parseExpr()
      ann match
        case Some(ty) => ELet(name, EAscribe(rhs, ty), body)
        case None => ELet(name, rhs, body)

  private def parseLetRec(): Expr =
    expect(Kind.LetRec, "`letrec`")
    val name = parseIdentifier("recursive binding name")
    val binders = parseHeaderBinders()

    if binders.nonEmpty then
      val retTy = parseOptionalTypeAnnotation()
      expect(Kind.Equal, "`=`")
      val rhsBody = parseExpr()
      expect(Kind.In, "`in`")
      val body = parseExpr()

      val rhs = buildHeaderRhs(binders, retTy, rhsBody)
      val rhsWithAnn =
        retTy match
          case Some(ty) => EAscribe(rhs, buildHeaderType(binders, ty))
          case None => rhs // Note: this is the case letrec defines a function without explicitly annotating the result type.
      ELetRec(name, rhsWithAnn, body)
    else
      val ann = parseOptionalTypeAnnotation()
      expect(Kind.Equal, "`=`")
      val rhs = parseExpr()
      expect(Kind.In, "`in`")
      val body = parseExpr()
      ann match
        case Some(ty) => ELetRec(name, EAscribe(rhs, ty), body)
        case None => ELetRec(name, rhs, body)

  private def parseFun(): Expr =
    expect(Kind.Fun, "`fun`")
    val stage = parseOptionalStageValue()
    expect(Kind.LParen, "`(`")
    val arg = parseIdentifier("parameter name")
    expect(Kind.Colon, "`:` after function parameter")
    val argTy = parseTypeExpr()
    expect(Kind.RParen, "`)`")
    val retTy = parseOptionalTypeAnnotation()
    expect(Kind.FatArrow, "`=>`")
    val lam = ELam(arg, Some(argTy), parseExpr(), retTy)
    stage match
      case None | Some(Sta) => lam
      case Some(st) => ELift(lam, st)

  private def parseSFun(): Expr =
    expect(Kind.SFun, "`sfun`")
    expect(Kind.LBracket, "`[`")
    val st = parseIdentifier("stage variable")
    expect(Kind.RBracket, "`]`")
    val ann = parseOptionalTypeAnnotation()
    expect(Kind.FatArrow, "`=>`")
    val lam = ESLam(st, parseExpr())
    ann.foreach(lam.withType)
    lam

  private def parseFix(): Expr =
    expect(Kind.Fix, "`fix`")
    val stage = parseOptionalStageValue()
    val name = parseIdentifier("fixpoint name")
    expect(Kind.Dot, "`.`")
    EFix(name, parseExpr(), stage)

  private def parseIf(): Expr =
    expect(Kind.If, "`if`")
    val stage = parseOptionalStageValue()
    val cond = parseExpr()
    expect(Kind.Then, "`then`")
    val thn = parseExpr()
    expect(Kind.Else, "`else`")
    val els = parseExpr()
    ECond(cond, thn, els, stage)

  private def parseComparison(): Expr =
    var expr = parseAdditive()
    while
      current.kind match
        case Kind.LessEq | Kind.GreaterEq | Kind.Less | Kind.Greater | Kind.EqEq | Kind.BangEq => true
        case _ => false
    do
      val op = advance().lexeme
      val stage = parseOptionalStageValue()
      val rhs = parseAdditive()
      expr = EBinOp(op, expr, rhs, stage)
    expr

  private def parseAdditive(): Expr =
    var expr = parseMultiplicative()
    while at(Kind.Plus) || at(Kind.Minus) do
      val op = advance().lexeme
      val stage = parseOptionalStageValue()
      val rhs = parseMultiplicative()
      expr = EBinOp(op, expr, rhs, stage)
    expr

  private def parseMultiplicative(): Expr =
    var expr = parseUnary()
    while at(Kind.Star) || at(Kind.Slash) do
      val op = advance().lexeme
      val stage = parseOptionalStageValue()
      val rhs = parseUnary()
      expr = EBinOp(op, expr, rhs, stage)
    expr

  private def parseUnary(): Expr =
    if at(Kind.Minus) then
      advance()
      val stage = parseOptionalStageValue()
      if at(Kind.IntLit) then ENum(-advance().lexeme.toInt)
      else EUnaryOp("-", parseUnary(), stage)
    else if at(Kind.Bang) then
      advance()
      val stage = parseOptionalStageValue()
      EDeref(parseUnary(), stage)
    else
      parseApplication()

  private def parseApplication(): Expr =
    var expr = parseAtomicPostfix()
    var keepGoing = true
    while keepGoing do
      current.kind match
        case Kind.LBracket =>
          val stages = parseBracketedStages()
          stages.foreach(stage => expr = ESApp(expr, stage))
        case Kind.LParen =>
          advance()
          val arg = parseExpr()
          expect(Kind.RParen, "`)`")
          expr = EApp(expr, arg, parseOptionalStageValue())
        case kind if canStartJuxtapositionArg(kind) =>
          val arg = parseJuxtapositionArg()
          expr = EApp(expr, arg, parseOptionalStageValue())
        case _ =>
          keepGoing = false
    expr

  private def parseAtomicPostfix(): Expr =
    var expr = parsePrimary()
    while at(Kind.LBracket) do
      val stages = parseBracketedStages()
      stages.foreach(stage => expr = ESApp(expr, stage))
    expr

  private def parseJuxtapositionArg(): Expr =
    parseAtomicPostfix()

  private def canStartJuxtapositionArg(kind: Kind): Boolean =
    kind match
      case Kind.IntLit | Kind.True | Kind.False | Kind.Identifier | Kind.Lift | Kind.Ref | Kind.IsApp | Kind.Run => true
      case _ => false

  private def parsePrimary(): Expr =
    current.kind match
      case Kind.IntLit =>
        ENum(advance().lexeme.toInt)
      case Kind.True =>
        advance()
        EBool(true)
      case Kind.False =>
        advance()
        EBool(false)
      case Kind.Identifier =>
        EVar(advance().lexeme)
      case Kind.Lift =>
        parseLift()
      case Kind.Ref =>
        parseRef()
      case Kind.IsApp =>
        parseIsApp()
      case Kind.Run =>
        parseRun()
      case Kind.LParen =>
        parseParenExpr()
      case _ =>
        fail(s"Unexpected token `${current.lexeme}`")

  private def parseLift(): Expr =
    expect(Kind.Lift, "`lift`")
    val stage = parseBracketedStage()
    expect(Kind.LParen, "`(`")
    val expr = parseExpr()
    expect(Kind.RParen, "`)`")
    ELift(expr, stage)

  private def parseRef(): Expr =
    expect(Kind.Ref, "`ref`")
    val stage = parseOptionalStageValue()
    expect(Kind.LParen, "`(`")
    val expr = parseExpr()
    expect(Kind.RParen, "`)`")
    EAlloc(expr, stage)

  private def parseIsApp(): Expr =
    expect(Kind.IsApp, "`isApp`")
    expect(Kind.LParen, "`(`")
    val expr = parseExpr()
    expect(Kind.RParen, "`)`")
    EIsApp(expr)

  private def parseRun(): Expr =
    expect(Kind.Run, "`run`")
    expect(Kind.LParen, "`(`")
    val expr = parseExpr()
    expect(Kind.RParen, "`)`")
    ERun(expr)

  private def parseParenExpr(): Expr =
    expect(Kind.LParen, "`(`")
    if at(Kind.RParen) then
      advance()
      EUnit
    else
      val expr = parseExpr()
      if at(Kind.Colon) then
        advance()
        val ty = parseTypeExpr()
        expect(Kind.RParen, "`)`")
        EAscribe(expr, ty)
      else
        expect(Kind.RParen, "`)`")
        expr

  private def parseTypeExpr(): Type =
    current.kind match
      case Kind.Forall =>
        advance()
        expect(Kind.LBracket, "`[`")
        val st = parseIdentifier("stage variable")
        expect(Kind.RBracket, "`]`")
        expect(Kind.Dot, "`.`")
        TForallSt(st, parseTypeExpr())
      case _ =>
        parseArrowType()

  private def parseArrowType(): Type =
    val lhs = parseAtType()
    if at(Kind.Arrow) then
      advance()
      TFun(lhs, parseArrowType())
    else
      lhs

  private def parseAtType(): Type =
    val base = parseAtomicType()
    if at(Kind.At) then
      advance()
      parseStage() match
        case SNum(1) => base
        case SNum(2) => TCode(base)
        case st => TAt(base, st)
    else
      base

  private def parseAtomicType(): Type =
    current.kind match
      case Kind.Identifier =>
        val name = advance().lexeme
        if at(Kind.LBracket) then
          advance()
          val arg = parseTypeExpr()
          expect(Kind.RBracket, "`]`")
          applyTypeConstructor(name, Some(arg))
        else
          applyTypeConstructor(name, None)
      case Kind.LParen =>
        advance()
        val ty = parseTypeExpr()
        expect(Kind.RParen, "`)`")
        ty
      case _ =>
        fail("Expected a type")

  private def applyTypeConstructor(name: String, arg: Option[Type]): Type =
    (name, arg) match
      case ("Unit", None) => TUnit
      case ("Int", None) => TInt
      case ("Bool", None) => TBool
      case ("Ref", Some(t)) => TRef(t)
      case ("Code", Some(t)) => TCode(t)
      case ("Code", None) =>
        fail("`Code` must be applied as `Code[T]`")
      case ("Ref", None) =>
        fail("`Ref` must be applied as `Ref[T]`")
      case _ =>
        fail(s"Unsupported type constructor `$name` for CoreEffOpt")

  private def parseOptionalTypeAnnotation(): Option[Type] =
    if at(Kind.Colon) then
      advance()
      Some(parseTypeExpr())
    else
      None

  private def parseHeaderBinders(): List[HeaderBinder] =
    val out = ArrayBuffer.empty[HeaderBinder]
    var keepGoing = true
    while keepGoing do
      current.kind match
        case Kind.LBracket =>
          advance()
          val stageNames = ArrayBuffer.empty[String]
          stageNames += parseIdentifier("stage variable")
          while at(Kind.Comma) do
            advance()
            stageNames += parseIdentifier("stage variable")
          expect(Kind.RBracket, "`]`")
          stageNames.foreach(name => out += HeaderBinder.Stage(name))
        case Kind.LParen =>
          advance()
          val arg = parseIdentifier("parameter name")
          expect(Kind.Colon, "`:` after function parameter")
          val argTy = parseTypeExpr()
          expect(Kind.RParen, "`)`")
          out += HeaderBinder.Term(arg, argTy)
        case _ =>
          keepGoing = false
    out.toList

  private def buildHeaderRhs(binders: List[HeaderBinder], retTy: Option[Type], body: Expr): Expr =
    var pendingRet = retTy
    binders.foldRight(body) {
      case (HeaderBinder.Stage(name), acc) =>
        ESLam(name, acc)
      case (HeaderBinder.Term(name, ty), acc) =>
        val lam = ELam(name, Some(ty), acc, pendingRet)
        pendingRet = None
        lam
    }

  private def buildHeaderType(binders: List[HeaderBinder], retTy: Type): Type =
    binders.foldRight(retTy) {
      case (HeaderBinder.Stage(name), acc) => TForallSt(name, acc)
      case (HeaderBinder.Term(_, ty), acc) => TFun(ty, acc)
    }

  private def parseStage(): Stage =
    current.kind match
      case Kind.IntLit =>
        val n = advance().lexeme.toInt
        if n < 0 then fail("Stage indices must be non-negative")
        SNum(n)
      case Kind.Identifier =>
        SVar(advance().lexeme)
      case _ =>
        fail("Expected a stage")

  private def parseOptionalStageValue(): Option[Stage] =
    if at(Kind.At) then
      advance()
      Some(parseStage())
    else
      None

  private def parseBracketedStage(): Stage =
    expect(Kind.LBracket, "`[`")
    val st = parseStage()
    expect(Kind.RBracket, "`]`")
    st

  private def parseBracketedStages(): List[Stage] =
    expect(Kind.LBracket, "`[`")
    val stages = ArrayBuffer.empty[Stage]
    stages += parseStage()
    while at(Kind.Comma) do
      advance()
      stages += parseStage()
    expect(Kind.RBracket, "`]`")
    stages.toList

  private def parseIdentifier(expected: String): String =
    if at(Kind.Identifier) then advance().lexeme
    else fail(s"Expected $expected")
