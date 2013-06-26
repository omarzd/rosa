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

class FullInliner(reporter: Reporter, vcMap: Map[FunDef, VerificationCondition]) extends TransformerWithPC {
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

      val vc = vcMap(funDef)
      val fncBody = vc.body.get
      vars = vars ++ vc.localVars

      val arguments: Map[Expr, Expr] = funDef.args.map(decl => decl.toVariable).zip(args).toMap

      val newBody = replace(arguments + (ResultVariable() -> fresh), fncBody)

      val constraint = newBody
      constraints = constraints :+ constraint
      fresh
    case _ =>
        super.rec(e, path)
  }

  def inlineFunctions(pre: Expr, body: Expr, post: Expr): (Expr, Expr, Expr, Set[Variable]) = {
    val (inlinedPre, cnstrPre, varsPre) = inlineFncCalls(pre)
    val (inlinedPost, cnstrPost, varsPost) = inlineFncCalls(post)
    val (inlinedBody, cnstrBody, varsBody) = inlineFncCalls(body)

    //cntrs are the function bodies
    (And(inlinedPre, And(cnstrPre)), And(inlinedBody, And(cnstrPost ++ cnstrBody)), inlinedPost, varsPre ++ varsPost ++ varsBody)
  }

  //@return (expr with inlined post, contraints on fresh variables, fresh variables used)
  def inlineFncCalls(expr: Expr): (Expr, Seq[Expr], Set[Variable]) = {
    constraints = Seq[Expr]()
    vars = Set[Variable]()
    val inlinedExpr = this.transform(expr)
    (inlinedExpr, constraints, vars)
  }


}