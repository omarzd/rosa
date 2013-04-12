package leon
package numerics

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._

import ceres.common.{Rational}

import Sat._

/**
  Something we need to prove.
  @param 
*/
case class VerificationCondition(val precondition: Expr, val expr: Expr,
  val postcondition: Expr, val funDef: FunDef, val inputs: Map[Variable, ParRange])  {
 
  /** The range and roundoff of the expression. */
  var res: Option[String] = None

  var time: Option[Double] = None
  var status: Sat = Unknown

}
