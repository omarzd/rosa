package leon
package numerics

import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import Valid._


// this will later also hold approximation info
class VerificationCondition(val funDef: FunDef) {

  //WithRoundoff
  var fncConstraintWR: Option[Expr] = None
  var validWR: Option[Valid] = None

  //Real arith only
  var fncConstraintRA: Option[Expr] = None
  var validRA: Option[Valid] = None

  var constraintGenTime: Option[Long] = None
}
