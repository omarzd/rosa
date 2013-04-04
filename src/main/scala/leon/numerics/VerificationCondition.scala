package leon
package numerics

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._

import ceres.common.{Rational}

import Sat._

case class VerificationCondition(val funDef: FunDef, val inputs: Map[Variable,
  ParRange], val expr: Expr, postCondition: Expr) {
  //, val output: Option[ParRange] = None,
  //val absRoundoff: Option[Rational] = None) {

  //assert( !(output.isEmpty && absRoundoff.isEmpty), "Empty VC, nothing to prove!")

  // for safekeeping the value of the expression
  var res: Option[XFloat] = None

  var time: Option[Double] = None
  var status: Sat = Unknown

}
