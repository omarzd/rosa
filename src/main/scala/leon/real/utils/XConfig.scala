/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import purescala.Trees._
import purescala.TreeOps._

case class XConfig(solver: RealRangeSolver, precondition: Expr, solverMaxIter: Int, solverPrecision: Rational,
  additionalConstraints: Set[Expr] = Set.empty) {
  
  def getCondition: Expr = And(precondition, And(additionalConstraints.toSeq))

  def addCondition(c: Expr): XConfig =
    new XConfig(solver, precondition, solverMaxIter, solverPrecision, additionalConstraints + c)

  def updatePrecision(newMaxIter: Int, newPrec: Rational): XConfig =
    new XConfig(solver, precondition, newMaxIter, newPrec, additionalConstraints)

  def and(other: XConfig): XConfig = {
    if (this.precondition == other.precondition)
      new XConfig(solver, precondition,
        math.max(solverMaxIter, other.solverMaxIter), Rational.min(solverPrecision, other.solverPrecision),
        this.additionalConstraints ++ other.additionalConstraints)
    else
      new XConfig(solver, precondition,
        math.max(solverMaxIter, other.solverMaxIter), Rational.min(solverPrecision, other.solverPrecision),
        this.additionalConstraints ++ other.additionalConstraints ++ Set(other.precondition))
  }

  def freshenUp(freshVars: Map[Expr, Expr]): XConfig = {
    XConfig(solver, replace(freshVars, precondition), solverMaxIter, solverPrecision, additionalConstraints.map(c => replace(freshVars, c)))
  }
  
}