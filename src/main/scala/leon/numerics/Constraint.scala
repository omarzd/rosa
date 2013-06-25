package leon
package numerics

import ceres.common.{Rational, RationalInterval}

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import Valid._

import Utils._
import ApproximationType._

// This is an approximation of an constraint.
// vars: additional free variables created
case class ConstraintApproximation(pre: Expr, body: Expr, post: Expr, vars: Set[Variable], tpe: ApproximationType) {
  var values: Map[Expr, (RationalInterval, Rational)] = Map.empty

  lazy val paths = collectPaths(body)
  override def toString: String = "APP(%s && %s) ==> %s".format(pre.toString, body.toString, post.toString)
}

// An original (unapproximated constraint) derived from somewhere in the program.
case class Constraint(pre: Expr, body: Expr, post: Expr, description: String) {
  var status: Option[Valid] = None
  var model: Option[Map[Identifier, Expr]] = None
  var strategy: String = ""

  def numVariables: Int = variablesOf(pre).size + variablesOf(body).size
  def size: Int = formulaSize(pre) + formulaSize(body)

  def solved: Boolean = status match {
    case Some(VALID) => true
    case Some(INVALID) => false
    case _ => false
  }

  lazy val paths = collectPaths(body)


  var approxStrategy =
    if (containsFunctionCalls(body) || containsFunctionCalls(pre) || containsFunctionCalls(post)) {
      //Seq(Uninterpreted_None, PostInlining_None, PostInlining_AA, FullInlining_None, FullInlining_AA)
      Seq(PostInlining_None, PostInlining_AA, FullInlining_None, FullInlining_AA)
    } else {
      Seq(Uninterpreted_None, NoFncs_AA)
      //Seq(NoFncs_AA)
    }

  def hasNextApproximation = !approxStrategy.isEmpty

  def getNextApproxType: Option[ApproximationType] = {
    if (approxStrategy.isEmpty) None
    else {
      val s = approxStrategy.head
      approxStrategy = approxStrategy.tail
      Some(s)
    }
  }

  var approximations = Seq[ConstraintApproximation]()


  // whether we already ran the AA approximation
  def approximationForSpec: Option[ConstraintApproximation] = {
    approximations.find(a => a.tpe == PostInlining_AA)
  }

  def overrideStatus(s: (Option[Valid], Option[Map[Identifier, Expr]])) = {
    status = s._1
    model = s._2
  }

  override def toString: String = "(%s && %s) ==> %s".format(pre.toString, body.toString, post.toString)

}


