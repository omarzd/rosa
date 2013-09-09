/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import purescala.Trees._
import purescala.TreeOps._

case class XConfig(val solver: RealSolver, val precondition: Expr, val solverMaxIter: Int, val solverPrecision: Rational,
  val additionalConstraints: Set[Expr] = Set.empty) {
  def getCondition: Expr = And(precondition, And(additionalConstraints.toSeq))

  def and(other: XConfig): XConfig = {
    if (this.precondition == other.precondition)
      new XConfig(solver, precondition, solverMaxIter, solverPrecision, this.additionalConstraints ++ other.additionalConstraints)
    else
      new XConfig(solver, precondition, solverMaxIter, solverPrecision, this.additionalConstraints ++ other.additionalConstraints ++ Set(other.precondition))
  }

  def addCondition(c: Expr): XConfig =
    new XConfig(solver, precondition, solverMaxIter, solverPrecision, additionalConstraints + c)

}




/*class XFloatConfig(s: RealSolver, prec: Expr, precision: Precision, machineEps: Rational, 
  slvMaxIter: Int, slvPrecision: Rational, addCnstr: Set[Expr] = Set.empty) extends XConfig(s, prec, slvMaxIter, slvPrecision, addCnstr) {

  override def and(other: XFloatConfig): XFloatConfig = {
    if (this.precondition == other.precondition)
      new XFloatConfig(solver, precondition, precision, machineEps, solverMaxIter, solverPrecision,
        this.additionalConstraints ++ other.additionalConstraints)
    else
      new XFloatConfig(solver, precondition, precision, machineEps, solverMaxIter, solverPrecision,
       this.additionalConstraints ++ other.additionalConstraints ++ Set(other.precondition))
  }

  override def addCondition(c: Expr): XFloatConfig =
    new XFloatConfig(solver, precondition, precision, machineEps, solverMaxIter, solverPrecision, additionalConstraints + c)


  def updatePrecision(newMaxIter: Int, newPrec: Rational): XFloatConfig =
    new XFloatConfig(solver, precondition, precision, machineEps, newMaxIter, newPrec, additionalConstraints)

  def freshenUp(freshVars: Map[Expr, Expr]): XFloatConfig = {
    new XFloatConfig(solver, replace(freshVars, precondition), precision, machineEps, solverMaxIter, solverPrecision,
      additionalConstraints.map(c => replace(freshVars, c)))
  }
}*/