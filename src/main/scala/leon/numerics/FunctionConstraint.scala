package leon
package numerics

import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._

// this will later also hold approximation info
class FunctionConstraint(val funDef: FunDef) {

  var fncConstraintWithRoundoff: Option[Expr] = None
  var fncConstraintRealArith: Option[Expr] = None
  var constraintGenTime: Option[Long] = None

  def formulaStats(expr: Option[Expr]): String = expr match {
    case Some(e) =>
      assert(variablesOf(e).size == allIdentifiers(e).size)
      "%d variables, formula size: %d".format(variablesOf(e).size, formulaSize(e))
    case None => " -- "
  }




}
