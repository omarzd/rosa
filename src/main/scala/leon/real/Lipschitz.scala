/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import Calculus._
import purescala.Trees._
import purescala.Common._
import purescala.TreeOps.{containsFunctionCalls, replace, preMap}

import real.TreeOps.{containsIfExpr}
import real.Trees._
import Rational._


class Lipschitz(reporter: Reporter, solver: RangeSolver) {
  implicit val debugSection = utils.DebugSectionLipschitz

  private def getLipschitzMatrix(preReal: Expr, fncs: Seq[Expr], ids: Seq[Identifier],
   vars: Map[Expr, RationalInterval]): RMatrix = {
  
    // have to inline, since we don't know (yet) how to do derivative with vals
    // however for the error computation, we keep the original form with vals,
    // since it seems to get better results
    val jacobian = EMatrix.fromSeqs(fncs.map(fnc => ids.map(id => d(inlineBody(fnc), id))))
    //println("jacobian: " + jacobian)
    
    val lipschitzConsts = jacobian.map(e => {
      val rangeDerivative = solver.getRange(preReal, e, vars,
                  solverMaxIterMedium, solverPrecisionMedium) 
       maxAbs(Seq(rangeDerivative.xlo, rangeDerivative.xhi))
      })
    //println("lipschitzConsts: " + lipschitzConsts)
    lipschitzConsts
  }

 /* private def getSigmaLipschitzMatrix(preReal: Expr, fncs: Seq[Expr],
    ids: Set[Identifier], precision: Precision): (Seq[Rational], RMatrix) = {
    
    // have to inline, since we don't know (yet) how to do derivative with vals
    // however for the error computation, we keep the original form with vals,
    // since it seems to get better results
    val jacobian = EMatrix.fromSeqs(fncs.map(fnc => ids.map(id => d(inlineBody(fnc), id))))
    //println("jacobian: " + jacobian)
    
    val transformer = new AAApproximator(reporter, solver, precision, checkPathError = false)//preReal, vc.variables, false, true)

    //println("############# idealToActual: " + idealToActual(updateFncs(0).rhs, vc.variables))
    val sigmas = fncs.map(fnc => transformer.computeError(idealToActual(fnc, vc.variables),
      preReal, vc.variables, exactInputs = true))
      //idealToActual(uf.rhs, vc.variables)))
    //println("sigmas: " + sigmas)
    
    val lipschitzConsts = jacobian.map(e => {
      val rangeDerivative = solver.getRange(preReal, e, vc.variables,
                  solverMaxIterMedium, solverPrecisionMedium) 
       maxAbs(Seq(rangeDerivative.xlo, rangeDerivative.xhi))
      })
    //println("lipschitzConsts: " + lipschitzConsts)
    (sigmas, lipschitzConsts)
  }
  */

  def getPropagatedError(precondition: Expr, es: Seq[Expr], vars: Map[Expr, XReal],
    ids: Seq[Identifier]): Option[Seq[Rational]] = {

    // TODO: duplicate in AAApproximator
    def rangeConstraint: Expr = {
      // TODO: check this (RealLiteral or FloatLiteral?)

      val clauses: Seq[Expr] = vars.flatMap({
        case (v, xreal) => Seq(LessEquals(RealLiteral(xreal.interval.xlo), v),
                                LessEquals(v, RealLiteral(xreal.interval.xhi)))
        }).toSeq
      And(clauses)
      //And(LessEquals(RealLiteral(i.xlo), v), LessEquals(v, RealLiteral(i.xhi)))
    }

    if (es.exists(e => containsIfExpr(e) || containsFunctionCalls(e)) ){
      reporter.warning("If or fnc call found, cannot apply Lipschitz.")
      None
    } else {
      // TODO: deduplication of clauses
      val completePre = And(precondition, rangeConstraint)
      val lipschitzConsts: RMatrix = getLipschitzMatrix(completePre, es, ids,
        vars.map(x => (x._1, x._2.interval)))

      //assert(lipschitzConsts.data.length == ids.length)

      reporter.debug("K: " + lipschitzConsts)

      val initErrors: Map[Identifier, Rational] = vars.map({
        case (Variable(id), xreal) => (id, xreal.maxError)
        })
      reporter.debug("initial errors: " + initErrors)

      // The sqrt is problematic, due to underflow
      /*val p2NormErrors: Seq[Rational] =
        lipschitzConsts.data.map(dta => {
          val rowSum = ids.zip(dta).foldLeft(zero){
            case (sum, (id, k)) => sum + (k*initErrors(id))*(k*initErrors(id)) 
          }
          println("rowSum: " + rowSum)
          println("sqrt: " + math.sqrt(rowSum.toDouble))
          println(sqrtUp(rowSum))
          sqrtUp(rowSum)
        })*/
      
      val infinityErrors: Seq[Rational] =
        lipschitzConsts.data.map(dta => {
          ids.zip(dta).foldLeft(zero){
            case (sum, (id, k)) => sum + k*initErrors(id) 
          }
        })

      val p1NormErrors: Seq[Rational] =
        lipschitzConsts.data.map(dta => {
          ids.zip(dta).foldLeft(zero){
            case (sum, (id, k)) => sum + k*initErrors(id) 
          }
        })
      reporter.info("lipschitz errors")
      reporter.info("p1 norm:  " + p1NormErrors)
      //reporter.info("p2 norm:  " + p2NormErrors)
      reporter.info("infinity: " + infinityErrors)  
      Some(infinityErrors)
    }
  }

  // Also needs to inline the FncVal's and keep track of the additional condition
  private def inlineBody(body: Expr): Expr = {
    var valMap: Map[Expr, Expr] = Map.empty
    val lastInstruction = preMap { expr => expr match {

        case Equals(v @ Variable(id), rhs) =>
          valMap = valMap + (v -> replace(valMap,rhs))
          Some(True)

        case x => Some(x)  //last instruction
      }
    }(body)
    //println("valMap: " + valMap)
    //println("last instruction: " + lastInstruction)
    val res = replace(valMap, lastInstruction)
    //println("res: " + res)
    res
  }

  private def maxAbs(nums: Seq[Rational]): Rational = nums match {
    case Seq(n) => abs(n)
    case _ => max(abs(nums.head), maxAbs(nums.tail))
  }

}