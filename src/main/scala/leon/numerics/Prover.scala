package leon
package numerics

import ceres.common.Rational

import purescala.Trees._

class Prover(reporter: Reporter) {


  def check(vc: VerificationCondition): VerificationCondition = {
    reporter.info("Now checking VC of function " + vc.funDef.id.name)

    val variables = variables2xfloats(vc.inputs)

    try {
      val exprResult = inXFloats(vc.expr, variables)
      reporter.info("result: " + exprResult)

      //TODO: check against the postcondition

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
  def variables2xfloats(vars: Map[Variable, ParRange]): Map[Variable, XFloat] = {
    vars.collect {
      case (k, v) if (v.isDefined) =>
        k -> XFloat(k, Rational.rationalFromReal(v.lo.get),
          Rational.rationalFromReal(v.hi.get))
    }
  }

  def inXFloats(tree: Expr, vars: Map[Variable, XFloat]): XFloat = tree match {
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
