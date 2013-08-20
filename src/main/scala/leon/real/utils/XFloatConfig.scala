/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import purescala.Trees._
import purescala.TreeOps._
import Precision._



case class XFloatConfig(solver: RealSolver, precondition: Expr, precision: Precision,
  machineEps: Rational, solverMaxIter: Int, solverPrecision: Rational, additionalConstraints: Set[Expr] = Set.empty) {

  def getCondition: Expr = And(precondition, And(additionalConstraints.toSeq))

  def addCondition(c: Expr): XFloatConfig =
    XFloatConfig(solver, precondition, precision, machineEps, solverMaxIter, solverPrecision, additionalConstraints + c)

  def updatePrecision(newMaxIter: Int, newPrec: Rational): XFloatConfig =
    XFloatConfig(solver, precondition, precision, machineEps, newMaxIter, newPrec, additionalConstraints)
  
  def and(other: XFloatConfig): XFloatConfig = {
    if (this.precondition == other.precondition)
      XFloatConfig(solver, precondition, precision, machineEps, solverMaxIter, solverPrecision,
        this.additionalConstraints ++ other.additionalConstraints)
    else
      XFloatConfig(solver, precondition, precision, machineEps, solverMaxIter, solverPrecision,
       this.additionalConstraints ++ other.additionalConstraints ++ Set(other.precondition))
  }

  def freshenUp(freshVars: Map[Expr, Expr]): XFloatConfig = {
    XFloatConfig(solver, replace(freshVars, precondition), precision, machineEps, solverMaxIter, solverPrecision,
      additionalConstraints.map(c => replace(freshVars, c)))
  }
}