package leon
package numerics

import purescala.Trees._

import ceres.common.{Rational, RationalInterval}

object TreeOps {

  def isMathFunction(expr: Expr): Boolean = expr match {
    case FloatLiteral(v) => true
    case IntLiteral(v) => true
    case FPlus(l, r) => isMathFunction(l) && isMathFunction(r)
    case FMinus(l, r) => isMathFunction(l) && isMathFunction(r)
    case FUMinus(e) => isMathFunction(e)
    case FTimes(l, r) => isMathFunction(l) && isMathFunction(r)
    case FDivision(l, r) => isMathFunction(l) && isMathFunction(r)
    case _ => false
    return true  
  }

  // This will need some partial bounds
  def extractVariableBounds(expr: Expr): Map[Variable, RationalInterval] = {
    //TODO
    return Map.empty
  }

  def getGoal(expr: Expr): (Option[RationalInterval], Option[Rational]) = {
    //TODO 
    return (None, None)
  }

}
