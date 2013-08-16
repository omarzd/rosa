/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import purescala.Definitions._
import purescala.Trees._

import real.Trees._
import real.RationalAffineUtils._

class Evaluator(ctx: LeonContext, program: Program, options: RealOptions) {
  val reporter = ctx.reporter
  private val solver = new NumericSolver(ctx, program, options.z3Timeout)

  def getRange(precond: Expr, expr: Expr, variables: VariableStore) = {
    // TODO: pre-process the expr (arithmetic ops)
    val approx = inIntervals(expr, variables)
    solver.tightenRange(expr, precond, approx, options.solverMaxIter, options.solverPrecision)
  }

  private def inIntervals(expr: Expr, vars: VariableStore): RationalInterval = expr match {
    case RationalLiteral(r) => RationalInterval(r, r)
    case v @ Variable(_) => vars.getInterval(v)
    case UMinusR(t) => - inIntervals(t, vars)
    case PlusR(l, r) => inIntervals(l, vars) + inIntervals(r, vars)
    case MinusR(l, r) => inIntervals(l, vars) - inIntervals(r, vars)
    case TimesR(l, r) => inIntervals(l, vars) * inIntervals(r, vars)
    case DivisionR(l, r) => inIntervals(l, vars) / inIntervals(r, vars)
    case SqrtR(t) =>
      val tt = inIntervals(t, vars)
      RationalInterval(sqrtDown(tt.xlo), sqrtUp(tt.xhi))     
  }

}