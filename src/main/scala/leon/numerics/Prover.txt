package leon
package numerics

import ceres.common.{RationalInterval, Rational}

import z3.scala._

import purescala.Trees._
import purescala.Common._
import purescala.TreeOps._
import purescala.TypeTrees.RationalType
import Sat._
import Valid._

object Prover {

  val resAbsRoundoff: Variable =
    Variable(FreshIdentifier("_resAbsRoundoff").setType(RationalType))

  val verbose = true
}

class Prover(reporter: Reporter, ctx: LeonContext, solver: NumericSolver) {
  import Prover._


  def check(vc: VerificationCondition): VerificationCondition = {

    def parseResult(result: (Sat, Z3Model)) = {
      result match {
        case (UNSAT, model) =>
          reporter.info(">>> VALID <<<")
          vc.updateStatus(VALID, reporter)
        case (SAT, model) =>
          reporter.info("Found counter-example: ")
          reporter.info(model)
          reporter.warning(">>> NOT SURE <<<")
          vc.updateStatus(NOT_SURE, reporter)
        case (Unknown, model) =>
          reporter.info(">>> Don't know <<<")
          vc.updateStatus(DUNNO, reporter)
      }
    }

    reporter.info("Now checking VC of function " + vc.funDef.id.name)

    val (variables, indices) = variables2xfloats(vc.inputs)

    reporter.info("Variable-index map: " + indices)
    vc.addComment("variables: " + indices.toString)

    val body = vc.expr
    val pre = vc.precondition
    val post = vc.postcondition

    solver.push
    solver.assertCnstr(vc.precondition)

    try {
      val t1 = System.nanoTime
      solver.countTimeouts = 0
      val exprResult: XFloat = inXFloats(vc.expr, variables)
      //vc.addComment("errors: " + exprResult.errorString(indices.values))

      /*val simpleCond = simpleTactic(exprResult.interval, exprResult.maxRoundoff, body, post)
      reporter.info("trying the simple tactic")
           
      val resultSimple = solver.check(Not(simpleCond))
      parseResult(resultSimple)  
 
      val genCond = generalTactic(exprResult.maxRoundoff, pre, body, post)
      reporter.info("trying the more general tactic")
    
      val resultGeneral = solver.check(Not(genCond))
      parseResult(resultGeneral)*/

      val numTimeouts = solver.countTimeouts
      vc.addComment("Num timeouts: " + numTimeouts)
      val t2 = System.nanoTime
      val dt = ((t2 - t1) / 1000000) / 1000.0 // should be secs

      reporter.info("result: " + exprResult)
      vc.res = Some(exprResult.toString)
      vc.time = Some(dt)
    }
    catch {
      case UnsupportedFragmentException(msg) =>
        reporter.info(msg)

      case ceres.affine.DivisionByZeroException(msg) =>
        reporter.info(msg)
    }
    // drop the VC precondition
    solver.pop
    vc
  }

  /**
    This tactic keeps the general idea of pre -> body \and post and only 
    extends it with roundoff errors to make it sound wrt. floats.
    pre: precondition \and "absRoundoff" \in [computed bounds]
    post: let result = body + absRoundoff in postcondition
    condition to check: pre -> post

    TODO: we have already computed a bound on the result range, can we reuse it?
   */
  private def generalTactic(roundoff: Rational, pre: Expr, body: Expr, post: Expr): Expr = {
    assert(roundoff >= Rational.zero, "absolute roundoff is negative: " + roundoff)

    // TODO: body has to be a simple arithmetic expression

    val rndoffFresh = Variable(FreshIdentifier("absRoundoff", true).setType(RationalType))
    val precondition = And(pre, And(GreaterEquals(rndoffFresh, RationalLiteral(-roundoff)),
                                    LessEquals(rndoffFresh, RationalLiteral(roundoff))))

    val floatBody = Plus(body, rndoffFresh)
    val resFresh = FreshIdentifier("result", true).setType(body.getType)

    val postTmp = replace(Map(AbsRoundoff(ResultVariable()) -> rndoffFresh), post)
    val bodyAndPost = Let(resFresh, floatBody,
      replace(Map(ResultVariable() -> Variable(resFresh)), postTmp))

    Implies(precondition, bodyAndPost)
  }


  /**
    Omit the function body completely and construct the condition to check
    as pre -> post, where
    - pre: result \in [computed bounds] \and absRoundoff \in [+/- computed bound]
    - post: postcondition[res -> "result", absRoundoff(res) -> "absRoundoff"]

    TODO: this seems to keep the variables from the body around too
  */
  private def simpleTactic(resBound: RationalInterval, roundoff: Rational,
    body: Expr, post: Expr): Expr = {

    val resFresh = Variable(FreshIdentifier("result", true).setType(body.getType))
    val rndoffFresh = Variable(FreshIdentifier("absRoundoff", true).setType(RationalType))
    val precondition = And(
        And(GreaterEquals(resFresh, RationalLiteral(resBound.xlo)),
            LessEquals(resFresh, RationalLiteral(resBound.xhi))),
        And(GreaterEquals(rndoffFresh, RationalLiteral(-roundoff)),
            LessEquals(rndoffFresh, RationalLiteral(roundoff))))

    val postTmp = replace(Map(AbsRoundoff(ResultVariable()) -> rndoffFresh), post)
    val postcondition = replace(Map(ResultVariable() -> resFresh), postTmp)
    Implies(precondition, postcondition)
  }



  // We can only create variables if we have both bounds defined.
  // We assume that the numbers written down by the user are meant to be reals.
  /*private def variables2xfloats(vars: Map[Variable, ParRange]): Map[Variable, XFloat] = {
    vars.collect {
      case (k, v) if (v.isDefined) =>
        k -> XFloat(k,
                    RationalInterval(Rational.rationalFromReal(v.lo.get),
                                     Rational.rationalFromReal(v.hi.get)),
                    solver)
    }
  }*/

  /**
    Converts partial ranges into XFloats.
    Only converts those ranges that are fully defined.
    Returns for each of those variables a XFloat and the index of its error.
   */
  private def variables2xfloats(vars: Map[Variable, ParRange]):
    (Map[Variable, XFloat], Map[Variable, Int]) = {
    var variableMap: Map[Variable, XFloat] = Map.empty
    var indexMap: Map[Variable, Int] = Map.empty

    for((k, v) <- vars) {
      if (v.isDefined) {
        val (xfloat, index) = XFloat.withIndex(k,
          RationalInterval(Rational.rationalFromReal(v.lo.get), Rational.rationalFromReal(v.hi.get)),
          solver)
        variableMap = variableMap + (k -> xfloat) 
        indexMap = indexMap + (k -> index)
      }
    }
    (variableMap, indexMap)
  }
  
  private def inXFloats(tree: Expr, vars: Map[Variable, XFloat]): XFloat = tree match {
    case v @ Variable(id) => vars(v)
    case RationalLiteral(v) => XFloat(v, solver) // not sure where this could come from atm...
    case IntLiteral(v) => XFloat(v, solver)
    case FloatLiteral(v) => XFloat(v, solver)
    case UMinus(rhs) => - inXFloats(rhs, vars)
    case Plus(lhs, rhs) => inXFloats(lhs, vars) + inXFloats(rhs, vars)
    case Minus(lhs, rhs) => inXFloats(lhs, vars) - inXFloats(rhs, vars)
    case Times(lhs, rhs) => inXFloats(lhs, vars) * inXFloats(rhs, vars)
    case Division(lhs, rhs) => inXFloats(lhs, vars) / inXFloats(rhs, vars)
    // TODO: IntegerAsFloat
    case _ =>
      throw UnsupportedFragmentException("Can't handle: " + tree.getClass)
      null
  }

}
