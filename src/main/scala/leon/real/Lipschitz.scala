/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import Calculus._
import purescala.Trees._
import purescala.Common._
import purescala.TreeOps.{containsFunctionCalls, replace, preMap, preTraversal}

import real.TreeOps.{containsIfExpr}
import real.Trees._
import Rational._


class Lipschitz(reporter: Reporter, solver: RangeSolver, leonToZ3: LeonToZ3Transformer) {
  implicit val debugSection = utils.DebugSectionLipschitz

  /*def getSigmaJacobianHessian(preReal: Expr, updateFncs: Seq[UpdateFunction],
    ids: Seq[Identifier], precision: Precision): (Seq[Rational], EMatrix, RMatrix, Seq[RMatrix]) = {

    val transformer = new Approximator(reporter, solver, precision, preReal, vc.variables, false, true)
    
    def boundRanges(m: EMatrix): RMatrix = {
      m.map(e => {
        val rangeDerivative = solver.getRange(preReal, e, vc.variables,
                  solverMaxIterMedium, solverPrecisionMedium) 
        maxAbs(Seq(rangeDerivative.xlo, rangeDerivative.xhi))
      })
    }

    // have to inline, since we don't know (yet) how to do derivative with vals
    // however for the error computation, we keep the original form with vals,
    // since it seems to get better results
    val jacobian = EMatrix.fromSeqs(updateFncs.map(uf => ids.map(id => d(inlineBody(uf.rhs), id))))
    //println("jacobian: " + jacobian)

    val hessians = getHessian(jacobian, ids)
    //println(hessians.mkString("\n"))
    
    

    //println("############# idealToActual: " + idealToActual(updateFncs(0).rhs, vc.variables))
    val sigmas = updateFncs.map(uf => transformer.computeError(idealToActual(uf.rhs, vc.variables)))
    println("sigmas: " + sigmas)
    
    val lipschitzConsts = boundRanges(jacobian)

    val hessianConsts = hessians.map( hessian => boundRanges(hessian))

    println("lipschitzConsts: " + lipschitzConsts)
    (sigmas, jacobian, lipschitzConsts, hessianConsts)
  }*/

  private def getLipschitzMatrix(preReal: Expr, fncs: Seq[Expr], ids: Seq[Identifier],
   vars: Map[Expr, RationalInterval]): RMatrix = {
  
    // have to inline, since we don't know (yet) how to do derivative with vals
    // however for the error computation, we keep the original form with vals,
    // since it seems to get better results
    println("preReal: " + preReal)
    println("ids: " + ids)

    val jacobian = EMatrix.fromSeqs(fncs.map(fnc => ids.map(id => d(inlineBody(fnc), id))))
    println("jacobian: " + jacobian)
    
    val lipschitzConsts = jacobian.map(e => {
      // The precondition and the vars need to take into account the ranges including x, \tl{x},
      // i.e. the ranges WITH all errors!
      val rangeDerivative = solver.getRange(preReal, e, vars, leonToZ3,
                  solverMaxIterMedium, solverPrecisionMedium) 
       maxAbs(Seq(rangeDerivative.xlo, rangeDerivative.xhi))
      })
    //println("lipschitzConsts: " + lipschitzConsts)
    lipschitzConsts
  }

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

  private def getValMapForInlining(body: Expr): Map[Expr, Expr] = {
    var valMap: Map[Expr, Expr] = Map.empty
    preTraversal { expr => expr match {
        case Equals(v @ Variable(id), rhs) =>
          valMap = valMap + (v -> replace(valMap,rhs))
        case _ => ;
      }
    }(body)
    valMap
  }

  /*
    @param n number of iterations
    @param lambda initial error
    @param sigma error of one loop iteration
    @param K Lipschitz constant
  */
  def errorFromNIterations(n: Int, lambda: Rational, sigma: Rational, k: Rational): Rational = {
    var kn = k
    for (i <- 1 until n) { kn *= k }

    kn * lambda + sigma * ((one - kn)/(one - k))
  }

  // assume that the updateFncs are ordered, same for ids
  //@param sigmas roundoff error on computing the update functions
  def getLoopError(preReal: Expr, body: Expr, ids: Seq[Identifier], updateFncs: Seq[Expr],
    vars: Map[Expr, XReal], sigmas: Seq[Rational], precision: Precision, loopBound: Option[Int]): Seq[Rational] = {

    println("body: " + body)
    println("updateFncs: " + updateFncs)

    // Inline model inputs
    var additionalVars: Map[Expr, Record] = Map()
    val (inlinedFncs, modelConstraints) = {
      var modelCnstrs = Set[Expr]()
      val body2 = preMap {
        //TODO: check that this is a model?
        case FncValue(specs, specExpr, true) =>
          assert(specs.length == 1)
          modelCnstrs += specExpr

          val (records, loopC, int) = VariablePool.collectVariables(specExpr)
          additionalVars = additionalVars + ((Variable(specs(0).id),
            records(Variable(specs(0).id))))
          
          Some(Variable(specs(0).id))
        case _ => None
      }(body)

      var valMap: Map[Expr, Expr] = getValMapForInlining(body2)

      (updateFncs.map { upfnc => replace(valMap, upfnc) }, modelCnstrs)
    }
    println("inlinedFncs: " + inlinedFncs)
    println("modelCnstrs: " + modelConstraints)
    println(And(modelConstraints.toSeq))
    
    // TODO: fix the precondition
    val mK = getLipschitzMatrix(And(preReal, And(modelConstraints.toSeq)), inlinedFncs, ids,
      vars.map(x => (x._1, x._2.interval)) ++ additionalVars.map(x => (x._1, RationalInterval(x._2.lo.get, x._2.up.get))))    
    reporter.info("sigmas: " + sigmas)
    reporter.info("K: " + mK)

    loopBound match {
      case Some(n) =>
        //val initErrorsMap = vc.variables.getInitialErrors(precision)
        val initErrorsMap: Map[Identifier, Rational] = vars.map({
          case (Variable(id), xreal) => (id, xreal.maxError)
        })
        reporter.debug("initial errors amp: " + initErrorsMap)

        val initErrors = ids.map(id => initErrorsMap(id))

        reporter.debug("ids: " + ids)
        reporter.debug("initErrors sorted: " + initErrors)

        val ks: Seq[Rational] = mK.rows.map(row => maxAbs(row))
        reporter.debug("ks: " + ks)
        val infinityNormErrors = sigmas.zip(ks).map( {
          case (s, k) => errorFromNIterations(n, maxAbs(initErrors), s, k)  
        })
        reporter.info("loop errors, infinity norm: \n" + infinityNormErrors)

        if (ids.length > 1) {
          val mKn = mK.power(n)
          reporter.debug("K^n: " + mKn)
          val mI = RMatrix.identity(ids.length)
          reporter.debug("I: " + mI)

          reporter.debug("(I-K)^-1: " + (mI - mK).inverse)
          val roundoffErrorMatrix = (((mI - mK).inverse) * (mI - mKn))
          reporter.debug("roundoffErrorMatrix: " + roundoffErrorMatrix)
          val roundoffErrors = roundoffErrorMatrix * sigmas
          val initialErrors = mKn * initErrors

          val componentwiseErrors = roundoffErrors.zip(initialErrors).map({
            case (a, b) => a + b
            })
          reporter.info("loop errors, componentwise: \n" + componentwiseErrors)
          val diff = infinityNormErrors.zip(componentwiseErrors).foldLeft(zero) {
            case (sum, (i, c)) => sum + (i - c)
          }
          if (diff < zero) {
            infinityNormErrors
          } else {
            componentwiseErrors
          }
        } else {
          infinityNormErrors
        }
        

      case _ => Seq.empty
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