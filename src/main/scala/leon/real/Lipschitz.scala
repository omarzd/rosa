/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import Calculus._
import purescala.Trees._
import purescala.Common._
import purescala.TreeOps.{containsFunctionCalls, replace, preMap, preTraversal}

import real.TreeOps._
import real.Trees._
import Rational._

// TODO: make this a trait?
class Lipschitz(reporter: Reporter, solver: RangeSolver, leonToZ3: LeonToZ3Transformer) {
  implicit val debugSection = utils.DebugSectionLipschitz

  def getPropagatedError(precondition: Expr, es: Seq[Expr], vars: Map[Expr, XReal],
    ids: Seq[Identifier]): Option[Seq[Rational]] = {

    if (es.exists(e => containsIfExpr(e) || containsFunctionCalls(e)) ){
      reporter.warning("If or fnc call found, cannot apply Lipschitz.")
      None
    } else {
      //TODO: can we add the additional constraints from the pre-condition?
      //val completePre = And(precondition, rangeConstraint(vars))
      val completePre = rangeConstraint(vars)
      println("precondition: " + precondition)
      println("completePre: " + completePre)
      
      println("es: " + es)
      val lipschitzConsts: RMatrix = getLipschitzMatrix(completePre, es, ids,
        vars.map(x => (x._1, x._2.interval)))
      reporter.debug("K: " + lipschitzConsts)

      val initErrors: Map[Identifier, Rational] = vars.map({
        case (Variable(id), xreal) => (id, xreal.maxError)
        })
      reporter.debug("initial errors: " + initErrors)

      // TODO: The sqrt is problematic, due to underflow
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

  // assume that the updateFncs are ordered, same for ids
  //@param sigmas roundoff error on computing the update functions
  def getLoopError(preReal: Expr, body: Expr, ids: Seq[Identifier], updateFncs: Seq[Expr],
    vars: Map[Expr, XReal], sigmas: Seq[Rational], precision: Precision, loopBound: Option[Int]): Seq[Rational] = {

    reporter.debug("computing loop error")
    reporter.debug("body: " + body)
    reporter.debug("updateFncs: " + updateFncs)

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
    reporter.debug("inlinedFncs: " + inlinedFncs)
    reporter.debug("modelCnstrs: " + modelConstraints)
    reporter.debug(And(modelConstraints.toSeq))
    
    // TODO: fix the precondition
    //println("preReal: " + preReal)
    //println("inlinedFncs: " + inlinedFncs)

    //println("pre: " + And(rangeConstraint(vars), And(modelConstraints.toSeq)) )
    val mK = getLipschitzMatrix(And(rangeConstraint(vars), And(modelConstraints.toSeq)), inlinedFncs, ids,
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

  def getTaylorError(preReal: Expr, ids: Seq[Identifier], expr: Expr, precision: Precision,
    sigmas: Seq[Rational], initErrors: Map[Identifier, Rational], vars: Map[Expr, RationalInterval]): Unit = {
    // TODO: deduplicate, make sure we have no scaling everywhere
    def p2Norm(s: Seq[Rational]): Rational = {
      val rowSum = s.foldLeft(zero){
          case (sum, elem) => sum + elem*elem
        }
      sqrtUpNoScaling(rowSum)
    }

    // check whether we can apply this
    // no ifs and no tuples (for now)
    if (containsIfExpr(expr) || containsFunctionCalls(expr)) {
      reporter.warning("Cannot apply Taylor error computation...")
      None
    } else {
      reporter.debug("initial errors: " + initErrors)
      println("initial errors: " + initErrors)

      // TODO: fix precondition
      val pre = rangeConstraintFromIntervals(vars) 
      val (jacobian, lipschitzConsts, hessianConsts) = getSigmaJacobianHessian(
        pre, expr, ids, precision, vars)
      assert(sigmas.length == 1 && lipschitzConsts.data.length == 1)

      println("jacobian: " + jacobian + "   * (sigma: "+sigmas(0)+")")
      
      println("hessian: " + hessianConsts)
      
      val h: Seq[Seq[Rational]] = hessianConsts.map(hc => hc.data.zipWithIndex.flatMap({
        case (row, i) =>
          row.zipWithIndex.map ({
            case (elem, j) =>
              println("computing: " + elem + " lambda " + i + ", " + j)
              elem * initErrors(ids(i)) * initErrors(ids(j))
            })
        }))

      assert(h.length == 1)
      val taylorRemainder = Rational(1, 2) * p2Norm(h(0)) 

      println("taylorRemainder: " + taylorRemainder)


      reporter.debug("K: " + lipschitzConsts)
      val sigma = sigmas(0)
      reporter.debug("sigma: " + sigma)
      
    }   
  } // end getTaylorError



  private def getLipschitzMatrix(preReal: Expr, fncs: Seq[Expr], ids: Seq[Identifier],
   vars: Map[Expr, RationalInterval]): RMatrix = {
  
    reporter.debug("preReal: " + preReal)
    reporter.debug("ids: " + ids)

    val jacobian = EMatrix.fromSeqs(fncs.map(fnc => ids.map(id => d(inlineBody(fnc), id))))
    reporter.debug("jacobian: " + jacobian)
    
    val lipschitzConsts = boundRanges(preReal, jacobian, vars)
    //reporter.debug("lipschitzConsts: " + lipschitzConsts)
    lipschitzConsts
  }

  
  private def getSigmaJacobianHessian(preReal: Expr, expr: Expr,
    ids: Seq[Identifier], precision: Precision, vars: Map[Expr, RationalInterval]):
      (EMatrix, RMatrix, Seq[RMatrix]) = {

    val inlinedExpr = inlineBody(expr)
    val jacobian = EMatrix.fromSeqs(Seq(ids.map(id => d(inlinedExpr, id))))
    reporter.debug("jacobian: " + jacobian)

    val hessians = getHessian(jacobian, ids)
    reporter.debug(hessians.mkString("\n"))
    
    val lipschitzConsts = boundRanges(preReal, jacobian, vars)

    val hessianConsts = hessians.map( hessian => boundRanges(preReal, hessian, vars))

    reporter.debug("lipschitzConsts: " + lipschitzConsts)
    (jacobian, lipschitzConsts, hessianConsts)
  }
  
  private def boundRanges(pre: Expr, m: EMatrix, vars: Map[Expr, RationalInterval]): RMatrix = {
    m.map(e => {
      val rangeDerivative = solver.getRange(pre, e, vars, leonToZ3,
                solverMaxIterMedium, solverPrecisionMedium) 
      maxAbs(Seq(rangeDerivative.xlo, rangeDerivative.xhi))
    })
  }

  private def getHessian(jacobian: EMatrix, ids: Seq[Identifier]): Seq[EMatrix] = {
    jacobian.data.map(row => {
      val elems = row.map( p => 
        ids.map(id =>  d(p, id) )
        )

      EMatrix.fromSeqs(elems)
      })
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

  /*
    @param n number of iterations
    @param lambda initial error
    @param sigma error of one loop iteration
    @param K Lipschitz constant
  */
  private def errorFromNIterations(n: Int, lambda: Rational, sigma: Rational, k: Rational): Rational = {
    var kn = k
    for (i <- 1 until n) { kn *= k }

    kn * lambda + sigma * ((one - kn)/(one - k))
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
}