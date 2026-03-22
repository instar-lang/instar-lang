package instar.codegen

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

import instar.interp.*
import instar.syntax.*
import Expr.*
import Stage.*
import Type.*
import Value.*

object CBackend:
  final class CompileException(message: String) extends RuntimeException(message)

  def compile(value: Value, store: Store = Map.empty): String =
    value match
      case VCode(expr) => Compiler(store).compileProgram(expr)
      case other => throw CompileException(s"Expected VCode, found $other")

  def compileResult(result: (Value, Store)): String =
    compile(result._1, result._2)

  private final class Compiler(store: Store):
    private var nextId = 0
    private val lambdaDefs = ArrayBuffer.empty[String]
    private val liftedLocDecls = ArrayBuffer.empty[String]
    private val liftedLocInits = ArrayBuffer.empty[String]
    private val liftedLocNames = mutable.LinkedHashMap.empty[Int, String]

    def compileProgram(expr: Expr): String =
      val body = new StringBuilder
      body.append("static Value instar_program(void) {\n")
      body.append("  Value result = make_unit();\n")
      body.append(emitExpr(stripAscriptions(expr), "result", Map.empty, "  "))
      body.append("  return result;\n")
      body.append("}\n")

      val out = new StringBuilder
      out.append(runtimePrelude)
      if liftedLocDecls.nonEmpty then
        liftedLocDecls.foreach(out.append)
        out.append('\n')
      lambdaDefs.foreach(out.append)
      out.append("static void init_lifted_locs(void) {\n")
      if liftedLocInits.isEmpty then
        out.append("  return;\n")
      else
        liftedLocInits.foreach(out.append)
      out.append("}\n\n")
      out.append(body.result())
      out.append(
        """int main(void) {
        |  init_lifted_locs();
        |  Value result = instar_program();
        |  print_value(result);
        |  printf("\n");
        |  return 0;
        |}
        """.stripMargin
      )
      out.result()

    private def emitExpr(expr: Expr, target: String, env: Map[String, String], indent: String): String =
      stripAscriptions(expr) match
        case ELet(x, rhs, body) =>
          val local = freshName("v")
          emitInto(local, declare = true, rhs, env, indent) +
            emitExpr(body, target, env + (x -> local), indent)

        case ECond(cond, thn, els, st) =>
          requireFirstStage(st, "conditionals")
          val condExpr = compileSimpleExpr(cond, env)
          val out = new StringBuilder
          out.append(s"${indent}if (as_bool($condExpr)) {\n")
          out.append(emitExpr(thn, target, env, indent + "  "))
          out.append(s"${indent}} else {\n")
          out.append(emitExpr(els, target, env, indent + "  "))
          out.append(s"${indent}}\n")
          out.result()

        case other =>
          emitInto(target, declare = false, other, env, indent)

    private def emitInto(name: String, declare: Boolean, expr: Expr, env: Map[String, String], indent: String): String =
      stripAscriptions(expr) match
        case lam @ ELam(_, _, _, _) =>
          emitLambdaInto(name, declare, lam, env, indent)

        case fix @ EFix(_, _, st) =>
          requireFirstStage(st, "fixpoints")
          emitFixInto(name, declare, fix, env, indent)

        case ECond(_, _, _, _) =>
          val prefix = if declare then s"${indent}Value $name = make_unit();\n" else ""
          prefix + emitExpr(expr, name, env, indent)

        case other =>
          val kw = if declare then "Value " else ""
          s"${indent}${kw}$name = ${compileSimpleExpr(other, env)};\n"

    private def emitLambdaInto(
      name: String,
      declare: Boolean,
      lam: ELam,
      env: Map[String, String],
      indent: String,
    ): String =
      val captures = lambdaCaptures(lam).toList.sorted
      val captureFields = captures.zipWithIndex.map { case (x, i) => x -> s"capture_$i" }
      val funName = freshName("lambda_fun")
      val envType = freshName("lambda_env")

      val funBodyEnv =
        Map(lam.x -> "arg") ++ captureFields.map { case (x, field) => x -> s"env->$field" }

      lambdaDefs += emitLambdaDef(funName, Some(envType), captureFields, lam.body, funBodyEnv)

      val out = new StringBuilder
      val envVar = freshName("env")
      if captures.isEmpty then
        val kw = if declare then "Value " else ""
        out.append(s"${indent}${kw}$name = make_closure(&$funName, NULL);\n")
      else
        out.append(s"${indent}$envType* $envVar = ($envType*)malloc(sizeof($envType));\n")
        out.append(s"${indent}if ($envVar == NULL) { instar_panic(\"out of memory\"); }\n")
        captureFields.foreach { case (x, field) =>
          out.append(s"${indent}$envVar->$field = ${lookupVar(x, env)};\n")
        }
        val kw = if declare then "Value " else ""
        out.append(s"${indent}${kw}$name = make_closure(&$funName, $envVar);\n")
      out.result()

    private def emitFixInto(
      name: String,
      declare: Boolean,
      fix: EFix,
      env: Map[String, String],
      indent: String,
    ): String =
      val (prefix, lam) = extractRecursiveLambda(fix.e)
      val prefixOut = new StringBuilder
      var currentEnv = env
      prefix.foreach { case (x, rhs) =>
        val local = freshName("v")
        prefixOut.append(emitInto(local, declare = true, rhs, currentEnv, indent))
        currentEnv += (x -> local)
      }

      val captures = recursiveLambdaCaptures(fix.f, lam).toList.sorted
      val captureFields = captures.zipWithIndex.map { case (x, i) => x -> s"capture_$i" }
      val funName = freshName("fix_fun")
      val envType = freshName("fix_env")

      val funBodyEnv =
        Map(lam.x -> "arg", fix.f -> "env->self") ++
          captureFields.map { case (x, field) => x -> s"env->$field" }

      lambdaDefs += emitLambdaDef(funName, Some(envType), captureFields, lam.body, funBodyEnv, recursive = true)

      val out = new StringBuilder
      out.append(prefixOut.result())
      val envVar = freshName("env")
      out.append(s"${indent}$envType* $envVar = ($envType*)malloc(sizeof($envType));\n")
      out.append(s"${indent}if ($envVar == NULL) { instar_panic(\"out of memory\"); }\n")
      captureFields.foreach { case (x, field) =>
        out.append(s"${indent}$envVar->$field = ${lookupVar(x, currentEnv)};\n")
      }
      val kw = if declare then "Value " else ""
      out.append(s"${indent}${kw}$name = make_closure(&$funName, $envVar);\n")
      out.append(s"${indent}$envVar->self = $name;\n")
      out.result()

    private def emitLambdaDef(
      funName: String,
      envType: Option[String],
      captureFields: List[(String, String)],
      body: Expr,
      env: Map[String, String],
      recursive: Boolean = false,
    ): String =
      val out = new StringBuilder
      envType.foreach { ty =>
        if recursive then
          out.append(s"typedef struct $ty {\n")
          out.append("  Value self;\n")
          captureFields.foreach { case (_, field) =>
            out.append(s"  Value $field;\n")
          }
          out.append(s"} $ty;\n")
        else if captureFields.nonEmpty then
          out.append(s"typedef struct $ty {\n")
          captureFields.foreach { case (_, field) =>
            out.append(s"  Value $field;\n")
          }
          out.append(s"} $ty;\n")
      }

      out.append(s"static Value $funName(void* env_ptr, Value arg) {\n")
      envType match
        case Some(ty) if recursive || captureFields.nonEmpty =>
          out.append(s"  $ty* env = ($ty*)env_ptr;\n")
        case _ =>
          out.append("  (void)env_ptr;\n")
      out.append("  Value result = make_unit();\n")
      out.append(emitExpr(stripAscriptions(body), "result", env, "  "))
      out.append("  return result;\n")
      out.append("}\n\n")
      out.result()

    private def compileSimpleExpr(expr: Expr, env: Map[String, String]): String =
      stripAscriptions(expr) match
        case EUnit => "make_unit()"
        case ENum(i) => s"make_int($i)"
        case EBool(b) => if b then "make_bool(1)" else "make_bool(0)"
        case EVar(x) => lookupVar(x, env)

        case EBinOp(op, e1, e2, st) =>
          requireFirstStage(st, s"binary op `$op`")
          s"${binOpName(op)}(${compileSimpleExpr(e1, env)}, ${compileSimpleExpr(e2, env)})"

        case EUnaryOp(op, e, st) =>
          requireFirstStage(st, s"unary op `$op`")
          s"${unaryOpName(op)}(${compileSimpleExpr(e, env)})"

        case EApp(e1, e2, st) =>
          requireFirstStage(st, "applications")
          s"apply_closure(${compileSimpleExpr(e1, env)}, ${compileSimpleExpr(e2, env)})"

        case EAlloc(e, st) =>
          requireFirstStage(st, "references")
          s"alloc_ref(${compileSimpleExpr(e, env)})"

        case EDeref(e, st) =>
          requireFirstStage(st, "dereference")
          s"read_ref(${compileSimpleExpr(e, env)})"

        case EAssign(e1, e2, st) =>
          requireFirstStage(st, "assignment")
          s"write_ref(${compileSimpleExpr(e1, env)}, ${compileSimpleExpr(e2, env)})"

        case ELoc(l) =>
          s"make_ref_cell(&${ensureLiftedLoc(l)})"

        case ELam(_, _, _, _) | EFix(_, _, _) | ECond(_, _, _, _) | ELet(_, _, _) =>
          throw CompileException(s"Expected a simple ANF expression, found $expr")

        case unsupported =>
          throw CompileException(s"Unsupported code form in C backend: $unsupported")

    private def ensureLiftedLoc(loc: Int): String =
      liftedLocNames.getOrElseUpdate(loc, {
        val cellName = s"lifted_loc_$loc"
        liftedLocDecls += s"static Value $cellName;\n"
        val initValue = store.get(loc) match
          case Some(value) => compileStaticValue(value)
          case None => throw CompileException(s"Missing store entry for lifted location $loc")
        liftedLocInits += s"  $cellName = $initValue;\n"
        cellName
      })

    private def compileStaticValue(value: Value): String =
      value match
        case VUnit => "make_unit()"
        case VNum(i) => s"make_int($i)"
        case VBool(b) => if b then "make_bool(1)" else "make_bool(0)"
        case VLoc(loc) => s"make_ref_cell(&${ensureLiftedLoc(loc)})"
        case other => throw CompileException(s"Unsupported lifted store value: $other")

    private def lambdaCaptures(lam: ELam): Set[String] =
      stripAscriptions(lam.body).freeVar - lam.x

    private def recursiveLambdaCaptures(f: String, lam: ELam): Set[String] =
      (stripAscriptions(lam.body).freeVar - lam.x) - f

    private def extractRecursiveLambda(expr: Expr): (List[(String, Expr)], ELam) =
      def loop(current: Expr, acc: List[(String, Expr)]): (List[(String, Expr)], ELam) =
        stripAscriptions(current) match
          case lam @ ELam(_, _, _, _) =>
            (acc.reverse, lam)

          case ELet(x, rhs, body) =>
            loop(body, (x -> rhs) :: acc)

          case EVar(x) =>
            acc match
              case (y, rhs) :: rest if x == y =>
                stripAscriptions(rhs) match
                  case lam @ ELam(_, _, _, _) => (rest.reverse, lam)
                  case other =>
                    throw CompileException(s"Recursive function must evaluate to a lambda, found $other")
              case _ =>
                throw CompileException(s"Recursive function must end in a lambda-bound variable, found $current")

          case other =>
            throw CompileException(s"Unsupported recursive function shape: $other")

      loop(expr, Nil)

    private def stripAscriptions(expr: Expr): Expr =
      expr match
        case EAscribe(e, _) => stripAscriptions(e)
        case other => other

    private def lookupVar(name: String, env: Map[String, String]): String =
      env.getOrElse(name, throw CompileException(s"Unbound variable during code generation: $name"))

    private def requireFirstStage(stage: Option[Stage], context: String): Unit =
      stage match
        case None | Some(Sta) => ()
        case Some(other) =>
          throw CompileException(s"C backend only supports first-stage ANF $context, found stage $other")

    private def binOpName(op: String): String =
      op match
        case "+" => "bin_add"
        case "-" => "bin_sub"
        case "*" => "bin_mul"
        case "/" => "bin_div"
        case "<=" => "bin_le"
        case ">=" => "bin_ge"
        case "<" => "bin_lt"
        case ">" => "bin_gt"
        case "==" => "bin_eq"
        case "!=" => "bin_ne"
        case _ => throw CompileException(s"Unsupported binary operator `$op`")

    private def unaryOpName(op: String): String =
      op match
        case "-" => "unary_neg"
        case _ => throw CompileException(s"Unsupported unary operator `$op`")

    private def freshName(prefix: String): String =
      val id = nextId
      nextId += 1
      s"${prefix}_$id"

    private val runtimePrelude = """
      |#include <inttypes.h>
      |#include <stdint.h>
      |#include <stdio.h>
      |#include <stdlib.h>
      |
      |typedef struct Value Value;
      |typedef Value (*InstarFun)(void* env, Value arg);
      |
      |typedef enum {
      |  TAG_UNIT,
      |  TAG_INT,
      |  TAG_BOOL,
      |  TAG_REF,
      |  TAG_CLOSURE
      |} Tag;
      |
      |typedef struct {
      |  InstarFun fun;
      |  void* env;
      |} Closure;
      |
      |struct Value {
      |  Tag tag;
      |  union {
      |    int64_t i;
      |    int b;
      |    Value* ref;
      |    Closure closure;
      |  } as;
      |};
      |
      |static void instar_panic(const char* msg) {
      |  fprintf(stderr, "%s\n", msg);
      |  exit(1);
      |}
      |
      |static Value make_unit(void) {
      |  Value value;
      |  value.tag = TAG_UNIT;
      |  return value;
      |}
      |
      |static Value make_int(int64_t i) {
      |  Value value;
      |  value.tag = TAG_INT;
      |  value.as.i = i;
      |  return value;
      |}
      |
      |static Value make_bool(int b) {
      |  Value value;
      |  value.tag = TAG_BOOL;
      |  value.as.b = b;
      |  return value;
      |}
      |
      |static Value make_ref_cell(Value* cell) {
      |  Value value;
      |  value.tag = TAG_REF;
      |  value.as.ref = cell;
      |  return value;
      |}
      |
      |static Value alloc_ref(Value init) {
      |  Value* cell = (Value*)malloc(sizeof(Value));
      |  if (cell == NULL) {
      |    instar_panic("out of memory");
      |  }
      |  *cell = init;
      |  return make_ref_cell(cell);
      |}
      |
      |static Value make_closure(InstarFun fun, void* env) {
      |  Value value;
      |  value.tag = TAG_CLOSURE;
      |  value.as.closure.fun = fun;
      |  value.as.closure.env = env;
      |  return value;
      |}
      |
      |static int64_t as_int(Value value) {
      |  if (value.tag != TAG_INT) {
      |    instar_panic("expected int");
      |  }
      |  return value.as.i;
      |}
      |
      |static int as_bool(Value value) {
      |  if (value.tag != TAG_BOOL) {
      |    instar_panic("expected bool");
      |  }
      |  return value.as.b;
      |}
      |
      |static Value* as_ref(Value value) {
      |  if (value.tag != TAG_REF) {
      |    instar_panic("expected ref");
      |  }
      |  return value.as.ref;
      |}
      |
      |static Closure as_closure(Value value) {
      |  if (value.tag != TAG_CLOSURE) {
      |    instar_panic("expected closure");
      |  }
      |  return value.as.closure;
      |}
      |
      |static Value apply_closure(Value fun, Value arg) {
      |  Closure closure = as_closure(fun);
      |  return closure.fun(closure.env, arg);
      |}
      |
      |static Value read_ref(Value ref) {
      |  return *as_ref(ref);
      |}
      |
      |static Value write_ref(Value ref, Value value) {
      |  *as_ref(ref) = value;
      |  return make_unit();
      |}
      |
      |static Value unary_neg(Value value) {
      |  return make_int(-as_int(value));
      |}
      |
      |static Value bin_add(Value left, Value right) {
      |  return make_int(as_int(left) + as_int(right));
      |}
      |
      |static Value bin_sub(Value left, Value right) {
      |  return make_int(as_int(left) - as_int(right));
      |}
      |
      |static Value bin_mul(Value left, Value right) {
      |  return make_int(as_int(left) * as_int(right));
      |}
      |
      |static Value bin_div(Value left, Value right) {
      |  return make_int(as_int(left) / as_int(right));
      |}
      |
      |static Value bin_le(Value left, Value right) {
      |  return make_bool(as_int(left) <= as_int(right));
      |}
      |
      |static Value bin_ge(Value left, Value right) {
      |  return make_bool(as_int(left) >= as_int(right));
      |}
      |
      |static Value bin_lt(Value left, Value right) {
      |  return make_bool(as_int(left) < as_int(right));
      |}
      |
      |static Value bin_gt(Value left, Value right) {
      |  return make_bool(as_int(left) > as_int(right));
      |}
      |
      |static Value bin_eq(Value left, Value right) {
      |  if (left.tag != right.tag) {
      |    return make_bool(0);
      |  }
      |  switch (left.tag) {
      |    case TAG_UNIT:
      |      return make_bool(1);
      |    case TAG_INT:
      |      return make_bool(left.as.i == right.as.i);
      |    case TAG_BOOL:
      |      return make_bool(left.as.b == right.as.b);
      |    case TAG_REF:
      |      return make_bool(left.as.ref == right.as.ref);
      |    case TAG_CLOSURE:
      |      return make_bool(
      |        left.as.closure.fun == right.as.closure.fun &&
      |        left.as.closure.env == right.as.closure.env
      |      );
      |  }
      |  instar_panic("unknown tag");
      |  return make_unit();
      |}
      |
      |static Value bin_ne(Value left, Value right) {
      |  Value eq = bin_eq(left, right);
      |  return make_bool(!as_bool(eq));
      |}
      |
      |static void print_value(Value value) {
      |  switch (value.tag) {
      |    case TAG_UNIT:
      |      printf("()");
      |      return;
      |    case TAG_INT:
      |      printf("%" PRId64, value.as.i);
      |      return;
      |    case TAG_BOOL:
      |      printf(value.as.b ? "true" : "false");
      |      return;
      |    case TAG_REF:
      |      printf("ref(");
      |      print_value(*value.as.ref);
      |      printf(")");
      |      return;
      |    case TAG_CLOSURE:
      |      printf("<closure>");
      |      return;
      |  }
      |  instar_panic("unknown tag");
      |}
      |""".stripMargin
