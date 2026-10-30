package instar.typing

import instar.syntax.*
import Stage.*
import Type.*

private[typing] object StageConstraints:
  private type Assignment = Map[String, Int]

  extension (constraints: List[StageConstraint])
    def implyStLeq(lower: Stage, upper: Stage): Boolean =
      val variables = (constraints.flatMap(c => Stage.variables(c.lower) ++ Stage.variables(c.upper)) ++
        Stage.variables(lower) ++ Stage.variables(upper)).distinct.sorted
      val satisfyingAssignments = allAssignments(variables).filter { assignment =>
        constraints.forall(constraint => satisfies(assignment, constraint))
      }
      satisfyingAssignments.forall { assignment =>
        satisfies(assignment, StageConstraint(lower, upper))
      }

    def implyStEq(a: Stage, b: Stage): Boolean =
      constraints.implyStLeq(a, b) && constraints.implyStLeq(b, a)

    def assertStLeq(lower: Stage, upper: Stage): Unit =
      assert(constraints.implyStLeq(lower, upper),
        s"stage constraint $lower <= $upper is not entailed")

    def implyCsEq(a: List[StageConstraint], b: List[StageConstraint]): Boolean =
      a.forall(c => (constraints ++ b).implyStLeq(c.lower, c.upper)) &&
        b.forall(c => (constraints ++ a).implyStLeq(c.lower, c.upper))

    def implyTyEq(left: Type, right: Type): Boolean =
      if !constraints.implyStEq(left.stage, right.stage) then false
      else (left.base, right.base) match
        case (TUnit, TUnit) | (TInt, TInt) | (TBool, TBool) => true
        case (TFun(la, lb), TFun(ra, rb)) =>
          constraints.implyTyEq(la, ra) && constraints.implyTyEq(lb, rb)
        case (TRef(a), TRef(b)) => constraints.implyTyEq(a, b)
        case (TForallSt(x, a, ac), TForallSt(y, b, bc)) =>
          val z = Counter.fresh
          val ac1 = Subst.constraints(ac, x, SVar(z))
          val bc1 = Subst.constraints(bc, y, SVar(z))
          constraints.implyCsEq(ac1, bc1) &&
            (constraints ++ ac1).implyTyEq(Subst.ty(a, x, SVar(z)), Subst.ty(b, y, SVar(z)))
        case _ => false

  private def allAssignments(variables: List[String]): Iterator[Assignment] = variables match
    case Nil => Iterator(Map.empty[String, Int])
    case name :: rest =>
      allAssignments(rest).flatMap { assignment =>
        Iterator(1, 2).map(stage => assignment + (name -> stage))
      }

  private def satisfies(assignment: Assignment, constraint: StageConstraint): Boolean =
    evaluate(constraint.lower, assignment) <= evaluate(constraint.upper, assignment)

  private def evaluate(stage: Stage, assignment: Assignment): Int = stage match
    case Stage.SNum(1) => 1
    case Stage.SNum(2) => 2
    case Stage.SVar(name) => assignment(name)
    case other => throw TypeException(s"unsupported stage $other; expected 1 or 2")
