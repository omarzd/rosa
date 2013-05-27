package leon
package numerics

import purescala.Trees._
import purescala.TreeOps._

import Valid._

class Prover(reporter: Reporter, solver: NumericSolver) {
  val verbose = false
  val absTransform = new AbsTransformer
  
  def check(vc: VerificationCondition) = {
    reporter.info("checking VC of " + vc.funDef.id.name)
  
    val (statusWR, modelWR) = feelingLucky(vc.fncConstraintWR)
    val (statusRA, modelRA) = feelingLucky(vc.fncConstraintRA)


    
    vc.statusWR = statusWR
    vc.modelWR = modelWR
    vc.statusRA = statusRA
    vc.modelRA = modelRA

  }

  // no approximation
  def feelingLucky(expr: Option[Expr]): (Option[Valid], Option[z3.scala.Z3Model]) = expr match {
    case Some(c) =>
      val constraint = absTransform.transform(c)
      if (verbose) println("\n expr before: " + c)
      if (verbose) println("\n expr after: " + constraint)
      
      val (valid, model) = solver.checkValid(constraint)
      (Some(valid), model)
    case None => (None, None)
  }


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
