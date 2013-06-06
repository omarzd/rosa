package leon
package numerics

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._

import Valid._

class Prover(reporter: Reporter, ctx: LeonContext, program: Program) {
  val verbose = true
  val absTransform = new AbsTransformer
  val solver = new NumericSolver(ctx, program)

  def check(vc: VerificationCondition) = {
    reporter.info("checking VC of " + vc.funDef.id.name)

    val start = System.currentTimeMillis
    for (constr <- vc.toCheck) {
      println("pre: " + constr.pre)
      println("body: " + constr.body)
      println("post: " + constr.post)

      // First try Z3 alone
      val (res, model) = feelingLucky(constr, vc.allVariables)
      constr.status = res
      constr.model = model
      // Then try XFloat alone

      // If neither work, do partial approx.

    }

    val totalTime = (System.currentTimeMillis - start)
    vc.verificationTime = Some(totalTime)
  }




  // no approximation
  def feelingLucky(c: Constraint, allVars: Seq[Variable]): (Option[Valid], Option[Map[Identifier, Expr]]) = {
    val toProve = Utils.exprToConstraint(allVars, c.pre, c.body, c.post, reporter)
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
