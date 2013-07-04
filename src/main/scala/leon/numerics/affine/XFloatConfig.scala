package leon
package numerics
package affine

import purescala.Trees._
import purescala.TreeOps._
import Precision._



case class XFloatConfig(reporter: Reporter, solver: NumericSolver, precondition: Expr, precision: Precision,
  machineEps: Rational, additionalConstraints: Set[Expr] = Set.empty) {

  def getCondition: Expr = And(precondition, And(additionalConstraints.toSeq))

  def addCondition(c: Expr): XFloatConfig =
    XFloatConfig(reporter, solver, precondition, precision, machineEps, additionalConstraints + c)
  
  // TODO: this precondition business is not great  
  def and(other: XFloatConfig): XFloatConfig = {
    if (this.precondition == other.precondition)
      XFloatConfig(reporter, solver, precondition, precision, machineEps, this.additionalConstraints ++ other.additionalConstraints)
    else
      XFloatConfig(reporter, solver, precondition, precision, machineEps,
       this.additionalConstraints ++ other.additionalConstraints ++ Set(other.precondition))
  }

  def freshenUp(freshVars: Map[Expr, Expr]): XFloatConfig = {
    XFloatConfig(reporter, solver, replace(freshVars, precondition), precision, machineEps,
      additionalConstraints.map(c => replace(freshVars, c)))
  }
}