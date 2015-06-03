/* Copthatright 2009-2015 EPFL, Lausanne */

package leon
package real

import purescala.Trees.{Expr, And, Equals, LessEquals}
import real.Trees._
import purescala.Trees.Expr
import Rational._
import VariableShop.getNewSqrtVariable
import real.TreeOps.{getClauses}
import purescala.TreeOps.{replace => replaceOps}

object RealRange {

  val solver = new RangeSolver(1000l)
  var solverTime = 0l

}

case class RealRange(tree: Expr, rangeApprox: RationalInterval, precond: Set[Expr],
  additionalConstr: Set[Expr]) {

  def addCondition(c: Expr): RealRange = RealRange(tree, this.interval, precond,
    additionalConstr + c)

  def replace(fresh: Map[Expr, Expr]): RealRange = 
    RealRange(replaceOps(fresh, tree), this.interval, precond.map(replaceOps(fresh, _ )), 
              additionalConstr.map(replaceOps(fresh, _)))

  // Removes any constraints that do not concern the variables in the tree expression
  def cleanConstraints: RealRange = {
    val clausesNeeded = TreeOps.removeRedundantConstraints(
      And((precond ++ additionalConstr).toSeq), tree)
    
    val preClauses = precond.flatMap(getClauses(_))
    val preNeeded = clausesNeeded.filter(cl => preClauses.contains(cl))
    
    val additionalNeeded = clausesNeeded -- preNeeded
    
    RealRange(tree, this.interval, preNeeded, additionalNeeded)
  }

  lazy val interval: RationalInterval = {
    val massagedTree = TreeOps.massageArithmetic(tree)
    val condition = And((precond ++ additionalConstr).toSeq)
    try {
      val start = System.currentTimeMillis
      val (res, timeout) = RealRange.solver.tightenRange(massagedTree, condition, rangeApprox)
      RealRange.solverTime += (System.currentTimeMillis - start)

      //println("after tightening: " + res)
      res //, if(timeout) 1 else 0)
    } catch {
      case e: java.lang.AssertionError =>
        println("Exception when tightening: " + tree)
        println("with precondition: " + condition)
        println(e.getMessage)
        throw UnsoundBoundsException("unsound range for " + tree)
        null
    }
  }

  def unary_-(): RealRange = RealRange(UMinusR(tree), -rangeApprox, precond, additionalConstr)

  def +(that: RealRange): RealRange = RealRange(PlusR(this.tree, that.tree), this.interval + that.interval,
                                              this.precond ++ that.precond,
                                              this.additionalConstr ++ that.additionalConstr)
  def -(that: RealRange): RealRange = RealRange(MinusR(this.tree, that.tree), this.interval - that.interval,
                                              this.precond ++ that.precond,
                                              this.additionalConstr ++ that.additionalConstr)
  def *(that: RealRange): RealRange = RealRange(TimesR(this.tree, that.tree), this.interval * that.interval,
                                              this.precond ++ that.precond,
                                              this.additionalConstr ++ that.additionalConstr)
  def /(that: RealRange): RealRange = RealRange(DivisionR(this.tree, that.tree), this.interval / that.interval,
                                              this.precond ++ that.precond,
                                              this.additionalConstr ++ that.additionalConstr)
  def squareRoot: RealRange = {
    // write sqrt as quadratic
    val newTree = getNewSqrtVariable
    val newCondition = And(Equals(TimesR(newTree, newTree), this.tree), LessEquals(RealLiteral(zero), newTree))

    RealRange(newTree, RationalInterval(sqrtDown(interval.xlo), sqrtUp(interval.xhi)),
              precond, additionalConstr  + newCondition)

  }

  def inverse: RealRange =
    RealRange(RealLiteral(one), RationalInterval(one, one), precond, additionalConstr) / this

}