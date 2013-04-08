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
     }
     catch {
       case UnsupportedFragmentException(msg) =>
         reporter.info(msg)

       case DivisionByZeroException(msg) =>
        reporter.info(msg)
     }
    vc
  }


  def variables2xfloats(vars: Map[Variable, ParRange]): Map[Variable, XFloat] = {

    vars.collect {
      case (k, v) if (v.isDefined) =>
        // TODO: this should be rounded outwards
        k -> XFloat(k, Rational(v.lo.get), Rational(v.hi.get))
    }
  }

  def inXFloats(tree: Expr, vars: Map[Variable, XFloat]): XFloat = tree match {
    case v @ Variable(id) => vars(v)
    case RationalLiteral(value) => XFloat(value) 
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
