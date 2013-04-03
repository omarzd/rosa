package leon
package numerics

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._

import ceres.common.{Rational}

case class VerificationCondition(val funDef: FunDef, val inputs: Map[Variable,
  ParRange], val expr: Expr, postCondition: Expr) {
  //, val output: Option[ParRange] = None,
  //val absRoundoff: Option[Rational] = None) {

  //assert( !(output.isEmpty && absRoundoff.isEmpty), "Empty VC, nothing to prove!")

  var time: Option[Double] = None
  var value: Option[Boolean] = None

}
