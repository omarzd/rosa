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