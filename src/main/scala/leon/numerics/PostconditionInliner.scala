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

class PostconditionInliner extends TransformerWithPC {
  type C = Seq[Expr]
  val initC = Nil

  var constraints = Seq[Expr]()

  // TODO: do we need this?
  def register(e: Expr, path: C) = path :+ e

  override def rec(e: Expr, path: C) = e match {
    case FunctionInvocation(funDef, args) =>
      val fresh = getNewFncVariable(funDef.id.name)

      funDef.postcondition match {
        case Some(post) =>
          val constraint = replace(Map(ResultVariable() -> fresh), post)
          constraints = constraints :+ constraint
        case None => ;
      }
      fresh

    case _ =>
        super.rec(e, path)
  }


}