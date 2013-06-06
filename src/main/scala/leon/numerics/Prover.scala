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
          val res = proveWithXFloat(constr, vc.inputs)
        case _ =>;
      }

      // If neither work, do partial approx.

    }

    val totalTime = (System.currentTimeMillis - start)
    vc.verificationTime = Some(totalTime)
  }

  private def proveWithXFloat(c: Constraint, inputs: Map[Variable, Record]): Option[Valid] = {
    reporter.info("Now trying with XFloat only...")

    val solver = new NumericSolver(ctx, program)
    solver.push
    // TODO: assert range bounds (later also other stuff)
    // TODO: make sure we push the correct bounds, i.e. not real-valued when it
    // was supposed to be floats and vice - versa
    //solver.assertCnstr(c.pre)

    // Create XFloat inputs
    val (variables, indices) = variables2xfloats(inputs, solver)
    println("variables: " + variables)
    println("indices: " + indices)

    val paths = collectPaths(c.body)
    println("paths")
    println(paths.mkString("\n"))

    // evaluate body


    // check if enough to prove post

    solver.pop
    None
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
