package leon
package numerics

import purescala.Definitions._
import purescala.Trees._

// this will later also hold approximation info
class FunctionConstraint(val funDef: FunDef, val constraint: Expr) {

  var genTime: Option[Long] = None
}
