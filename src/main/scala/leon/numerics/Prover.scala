package leon
package numerics

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._

import Valid._

class Prover(reporter: Reporter, ctx: LeonContext, program: Program) {
  val verbose = false
  val absTransform = new AbsTransformer
  val solver = new NumericSolver(ctx, program)
  
  def check(vc: VerificationCondition) = {
    reporter.info("checking VC of " + vc.funDef.id.name)
    val start = System.currentTimeMillis
    for (constr <- vc.toCheck) {
      val (res, model) = feelingLucky(constr.toProve)  
      constr.status = res
      constr.model = model
    }

    val totalTime = (System.currentTimeMillis - start)
    vc.verificationTime = Some(totalTime)
  }

  


  // no approximation
  def feelingLucky(expr: Expr): (Option[Valid], Option[Map[Identifier, Expr]]) = {
    val constraint = absTransform.transform(expr)
    if (verbose) println("\n expr before: " + expr)
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
