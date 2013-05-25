package leon
package numerics

import purescala.Definitions._
import purescala.Trees._

// this will later also hold approximation info
class FunctionConstraint(val funDef: FunDef) {

  var fncConstraintWithRoundoff: Option[Expr] = None
  var fncConstraintWithoutRoundoff: Option[Expr] = None
  var genTime: Option[Long] = None


}
