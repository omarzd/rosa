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
  /*
    We keep the expressions as given in the code, thus they contain doubles.
    The prover has to make sure that those are handled correctly. 
  */
  //assert( !(output.isEmpty && absRoundoff.isEmpty), "Empty VC, nothing to prove!")

  // for safekeeping the value of the expression
  var res: Option[String] = None

  var time: Option[Double] = None
  var status: Sat = Unknown

}
