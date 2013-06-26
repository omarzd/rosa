package leon
package numerics

import ceres.common._
import Rational.zero

import purescala.Trees._
import purescala.TypeTrees._
import purescala.TreeOps._
import purescala.Definitions._
import purescala.Common._

import RoundoffType._
import Utils._

class PostconditionInliner(reporter: Reporter) extends TransformerWithPC {
  type C = Seq[Expr]
  val initC = Nil

  var constraints = Seq[Expr]()
  var vars = Set[Variable]()

  // TODO: do we need this?
  def register(e: Expr, path: C) = path :+ e

  override def rec(e: Expr, path: C) = e match {
    case FunctionInvocation(funDef, args) =>
      val fresh = getNewFncVariable(funDef.id.name)
      vars = vars + fresh
      funDef.postcondition match {
        case Some(post) =>
          val constraint = replace(Map(ResultVariable() -> fresh), post)
          constraints = constraints :+ constraint
        case None =>
          reporter.warning("inlining postcondition, but none found for " + e)
      }
      fresh

    case _ =>
        super.rec(e, path)
  }

  def inlinePostcondition(pre: Expr, body: Expr, post: Expr): (Expr, Expr, Expr, Set[Variable]) = {
    val (inlinedPre, cnstrPre, varsPre) = inlineFncPost(pre)
    val (inlinedPost, cnstrPost, varsPost) = inlineFncPost(post)
    val (inlinedBody, cnstrBody, varsBody) = inlineFncPost(body)

    (And(inlinedPre, And(cnstrPre ++ cnstrBody)), inlinedBody, And(inlinedPost, And(cnstrPost)), varsPre ++ varsPost ++ varsBody)
  }

  //@return (expr with inlined post, contraints on fresh variables, fresh variables used)
  def inlineFncPost(expr: Expr): (Expr, Seq[Expr], Set[Variable]) = {
    constraints = Seq[Expr]()
    vars = Set[Variable]()
    val inlinedExpr = this.transform(expr)
    (inlinedExpr, constraints, vars)
  }

}