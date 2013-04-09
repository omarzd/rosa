package leon
package numerics

import ceres.common.Rational

import purescala.Trees._
import purescala.Common._
import purescala.TypeTrees.RationalType

object Prover {

  val resAbsRoundoff: Variable =
    Variable(FreshIdentifier("_resAbsRoundoff").setType(RationalType))
}

class Prover(reporter: Reporter) {
  import Prover._

  // check always pushes and pops so we can reuse one single solver
  val solver = new Solver

  def check(vc: VerificationCondition): VerificationCondition = {
    reporter.info("Now checking VC of function " + vc.funDef.id.name)

    val variables = variables2xfloats(vc.inputs)

    try {
      val exprResult: XFloat = inXFloats(vc.expr, variables)
      reporter.info("result: " + exprResult)
      vc.res = Some(exprResult)

      /*
      val resBound = exprResult.interval
      val resCondition =
        And(LessEquals(ResultVariable(), RationalLiteral(resBound.xhi)),
            GreaterEquals(ResultVariable(), RationalLiteral(resBound.xlo)))

      val rndoffCondition =
        And(LessEquals(IntLiteral(0), resAbsRoundoff),
          LessEquals(resAbsRoundoff, RationalLiteral(exprResult.maxRoundoff)))

      // postcondition is not empty, otherwise this VC would not exist
      val condition =
        if (vc.funDef.precondition.isEmpty) {
          Implies(And(resCondition, rndoffCondition), vc.postCondition)
        } else {
          // TODO: maybe filter out irrelevant stuff from the precondition/postcondition?
          Implies(And(vc.funDef.precondition.get, And(resCondition, rndoffCondition)),
            vc.postCondition)
        }

        val result = solver.check(condition)
        reporter.info("VC is " + result)
        vc.status = result*/
     }
     catch {
       case UnsupportedFragmentException(msg) =>
         reporter.info(msg)

       case ceres.affine.DivisionByZeroException(msg) =>
        reporter.info(msg)
     }
    vc
  }



  // We can only create variables if we have both bounds defined.
  // We assume that the numbers written down by the user are meant to be reals.
  private def variables2xfloats(vars: Map[Variable, ParRange]): Map[Variable, XFloat] = {
    vars.collect {
      case (k, v) if (v.isDefined) =>
        k -> XFloat(k, Rational.rationalFromReal(v.lo.get),
          Rational.rationalFromReal(v.hi.get))
    }
  }

  private def inXFloats(tree: Expr, vars: Map[Variable, XFloat]): XFloat = tree match {
    case v @ Variable(id) => vars(v)
    case RationalLiteral(v) => XFloat(v) // not sure where this could come from atm...
    case IntLiteral(v) => XFloat(v)
    case FloatLiteral(v) => XFloat(v)
    case FUMinus(rhs) => - inXFloats(rhs, vars)
    case FPlus(lhs, rhs) => inXFloats(lhs, vars) + inXFloats(rhs, vars)
    case FMinus(lhs, rhs) => inXFloats(lhs, vars) - inXFloats(rhs, vars)
    case FTimes(lhs, rhs) => inXFloats(lhs, vars) * inXFloats(rhs, vars)
    case FDivision(lhs, rhs) => inXFloats(lhs, vars) / inXFloats(rhs, vars)
    case _ =>
      throw UnsupportedFragmentException("Can't handle: " + tree.getClass)
      null
  }



}
