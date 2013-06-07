package leon
package numerics

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._

import Valid._
import Utils._

class Prover(reporter: Reporter, ctx: LeonContext, program: Program) {
  val verbose = true
  val absTransform = new AbsTransformer
  val solver = new NumericSolver(ctx, program)

  def check(vc: VerificationCondition) = {
    reporter.info("----------> checking VC of " + vc.funDef.id.name)

    val start = System.currentTimeMillis
    for (constr <- vc.toCheck) {
      println("pre: " + constr.pre)
      println("body: " + constr.body)
      println("post: " + constr.post)

      // First try Z3 alone
      //val (res, model) = feelingLucky(constr, vc.allVariables)
      //constr.status = res
      //constr.model = model

      // If Z3 failed ...
      constr.status match {
        case (None | Some(DUNNO) | Some(NOT_SURE)) =>
          // ... try XFloat alone
          val constraint = constraintWithXFloat(constr, vc.inputs)
          val (resAA, modelAA) = feelingLucky(constraint, vc.allVariables)
          println("REEESULT: " + resAA)
        case _ =>;
      }

      // If neither work, do partial approx.

    }

    val totalTime = (System.currentTimeMillis - start)
    vc.verificationTime = Some(totalTime)
  }

  private def constraintWithXFloat(c: Constraint, inputs: Map[Variable, Record]): Constraint = {
    reporter.info("Now trying with XFloat only...")

    val solver = new NumericSolver(ctx, program)

    val paths = collectPaths(c.body).map(p => p.addCondition(filterPreconditionForBoundsIteration(c.pre)))
    //println("paths")
    //println(paths.mkString("\n"))

    for (path <- paths) {
      //println("Investigating path: " + path)

      // TODO: make sure we push the correct bounds, i.e. not real-valued when it
      // was supposed to be floats and vice - versa
      val (variables, indices) = variables2xfloats(inputs, solver, path.condition)

      val result = inXFloats(path.expression, variables, solver, path.condition)
      path.value = Some(result(ResultVariable()))
      //println("result: " + result)
    }

    // Merge results from all branches
    val (interval, error) = mergePaths(paths)
    println("max interval: " + interval)
    println("max error: " + error)

    // Create constraint
    val newBodyConstraint = createConstraintFromResults(Map(ResultVariable() -> (interval, error)))
    println("constraint: " + newBodyConstraint)
    Constraint(And(c.pre, newBodyConstraint), BooleanLiteral(true), c.post)

  }


  // no approximation
  def feelingLucky(c: Constraint, allVars: Seq[Variable]): (Option[Valid], Option[Map[Identifier, Expr]]) = {
    reporter.info("Now trying with Z3 only...")
    val toProve = exprToConstraint(allVars, c.pre, c.body, c.post, reporter)
    val constraint = absTransform.transform(toProve)
    if (verbose) println("\n expr before: " + toProve)
    if (verbose) println("\n expr after: " + constraint)

    val (valid, model) = solver.checkValid(constraint)
    (Some(valid), model)
  }


  /*
    Translates the Abs(x) tree node into two inequalities.
  */
  class AbsTransformer extends TransformerWithPC {
    type C = Seq[Expr]
    val initC = Nil

    def register(e: Expr, path: C) = path :+ e

    override def rec(e: Expr, path: C) = e match {
      case LessEquals(Abs(expr), r @ RationalLiteral(value)) =>
        And(LessEquals(RationalLiteral(-value), expr),
          LessEquals(expr, r))
      case LessThan(Abs(expr), r @ RationalLiteral(value)) =>
        And(LessThan(RationalLiteral(-value), expr),
          LessThan(expr, r))
      case GreaterEquals(r @ RationalLiteral(value), Abs(expr)) =>
        And(LessEquals(RationalLiteral(-value), expr),
          LessEquals(expr, r))
      case GreaterThan(r @ RationalLiteral(value), Abs(expr)) =>
        And(LessThan(RationalLiteral(-value), expr),
          LessThan(expr, r))
      case _ =>
        super.rec(e, path)
    }

  }
}
