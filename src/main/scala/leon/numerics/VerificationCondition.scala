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
  var statusWR: Option[Valid] = None
  var modelWR: Option[z3.scala.Z3Model] = None

  //Real arith only
  var fncConstraintRA: Option[Expr] = None
  var statusRA: Option[Valid] = None
  var modelRA: Option[z3.scala.Z3Model] = None

  var constraintGenTime: Option[Long] = None
}
