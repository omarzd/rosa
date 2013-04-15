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

  val verbose = false
}

class Prover(reporter: Reporter, ctx: LeonContext, solver: NumericSolver) {
  import Prover._

  def check(vc: VerificationCondition): VerificationCondition = {

    def parseResult(result: (Sat, Z3Model)) = {
      result match {
        case (UNSAT, model) =>
          reporter.info(">>> VALID <<<")
          vc.status = VALID
        case (SAT, model) =>
          reporter.info("Found counter-example: ")
          reporter.info(model)
          reporter.error(">>> INVALID <<<")
          vc.status = INVALID
        case (Unknown, model) =>
          reporter.info(">>> Don't know <<<")
          vc.status = DUNNO
      }
    }

    reporter.info("Now checking VC of function " + vc.funDef.id.name)

    val variables = variables2xfloats(vc.inputs)
    val body = vc.expr
    val pre = vc.precondition
    val post = vc.postcondition

    solver.push
    solver.assertCnstr(vc.precondition)

    try {
      val t1 = System.nanoTime
      val exprResult: XFloat = inXFloats(vc.expr, variables)

      val simpleCond = simpleTactic(exprResult.interval, exprResult.maxRoundoff, body, post)
      if (verbose) println("simple condition: " + simpleCond)
           
      val result = solver.check(Not(simpleCond))
      parseResult(result)  
 
      val genCond = generalTactic(exprResult.maxRoundoff, pre, body, post)
      if (verbose) println("\ngeneral condition:" + genCond)
    
      val result1 = solver.check(Not(genCond))
      parseResult(result1)

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
  private def variables2xfloats(vars: Map[Variable, ParRange]): Map[Variable, XFloat] = {
    vars.collect {
      case (k, v) if (v.isDefined) =>
        k -> XFloat(k,
                    RationalInterval(Rational.rationalFromReal(v.lo.get),
                                     Rational.rationalFromReal(v.hi.get)),
                    solver)
    }
  }

  private def inXFloats(tree: Expr, vars: Map[Variable, XFloat]): XFloat = tree match {
    case v @ Variable(id) => vars(v)
    case RationalLiteral(v) => XFloat(v, solver) // not sure where this could come from atm...
    case IntLiteral(v) => XFloat(v, solver)
    case FloatLiteral(v) => XFloat(v, solver)
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
