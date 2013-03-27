package leon
package numerics

import purescala.Trees._

import ceres.common.{Rational, RationalInterval}

object TreeOps {

  def isMathFunction(expr: Expr): Boolean = {
    // TODO
    return true  
  }

  def extractVariableBounds(expr: Expr): Map[Variable, RationalInterval] = {
    //TODO
    return Map.empty
  }

  def getGoal(expr: Expr): (Option[RationalInterval], Option[Rational]) = {
    //TODO 
    return (None, None)
  }

}
