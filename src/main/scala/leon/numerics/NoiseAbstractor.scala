package leon
package numerics

import affine._
import Rational.zero

import purescala.Trees._
import purescala.TypeTrees._
import purescala.TreeOps._
import purescala.Definitions._
import purescala.Common._

import RoundoffType._
import Utils._
import VariableShop._

class NoiseAbstractor(reporter: Reporter, solver: NumericSolver, vcMap: Map[FunDef, VerificationCondition]) extends TransformerWithPC {
  type C = Seq[Expr]
  val initC = Nil

  var constraints = Seq[Expr]()
  var vars = Set[Variable]()

  def register(e: Expr, path: C) = path :+ e

  override def rec(e: Expr, path: C) = e match {
    case Equals(l, r) =>
      constraints = Seq[Expr]()
      val rhs = rec(r, path)

      val newExpr = if (constraints.isEmpty) Equals(l, r)
        else And(constraints :+ Equals(l, rhs))
      constraints = Seq[Expr]()
      newExpr

    case FunctionInvocation(funDef, args) =>
      val fresh = getNewFncVariable(funDef.id.name)
      vars = vars + fresh

      val vc = vcMap(funDef)
      val fncBody = vc.body
      vars = vars ++ vc.localVars

      val arguments: Map[Expr, Expr] = funDef.args.map(decl => decl.toVariable).zip(args).toMap
      val newBody = replace(arguments + (ResultVariable() -> fresh), fncBody)

      // Idea is to compute the noise on newBody here and only add the noise() constraint
      // We can do this path-by-path or just one


      val constraint = newBody
      constraints = constraints :+ constraint
      fresh
    case _ =>
        super.rec(e, path)
  }

  def transform(pre: Expr, body: Expr, post: Expr): (Expr, Expr, Expr, Set[Variable]) = {
    constraints = Seq[Expr]()
    vars = Set[Variable]()
    val newPre = rec(pre, initC)
    val cnstrPre = constraints

    constraints = Seq[Expr]()
    val newBody = rec(body, initC)
    val cnstrBody = constraints

    constraints = Seq[Expr]()
    val newPost = rec(post, initC)
    val cnstrPost = constraints

    (And(And(cnstrPre), newPre), And(And(cnstrBody), And(newBody, And(cnstrPost))), newPost, vars)
  }

}