package leon
package numerics

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._

import ceres.common.{Rational, RationalInterval}

/**
  Info about VCs that check whether an expression's result value is within
  a certain range and whether it's max abs roundoff is satisfied.
 */
case class VerificationCondition(val funDef: FunDef, val inputs: Map[Variable,
  RationalInterval], val expr: Expr, val output: Option[RationalInterval] = None,
  val absRoundoff: Option[Rational] = None) {

  assert( !(output.isEmpty && absRoundoff.isEmpty), "Empty VC, nothing to prove!")

  var time: Option[Double] = None
  var value: Option[Boolean] = None

}
