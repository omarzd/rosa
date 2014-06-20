/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import purescala.Trees._
import purescala.TypeTrees.{RealType}
import purescala.TreeOps._
import purescala.Common._

import real.Trees._
import real.TreeOps._
import XFloat.{variables2xfloats, variables2xfloatsExact, variables2xfloatsActualExact, xFloatWithUncertain}
import XFixed.{variables2xfixed, xFixedWithUncertain}
import VariableShop._
import Rational.max
import Precision._


// Manages the approximation
class AAApproximator(val reporter: Reporter, val solver: RangeSolver, precision: Precision, checkPathError: Boolean = true,
  useLipschitz: Boolean = false) extends Lipschitz {

  implicit override val debugSection = utils.DebugSectionAffine
  val compactingThreshold = 500


  //var variables: Map[Expr, XReal] = Map.empty

  var leonToZ3: LeonToZ3Transformer = null
  var inputVariables: VariablePool = null
  var initialCondition: Expr = True
  var config: XConfig = null
  var precondition: Expr = True

  private def init(inputs: VariablePool, precond: Expr) = {
    inputVariables = inputs
    precondition = precond
    leonToZ3 = new LeonToZ3Transformer(inputs, precision)
    initialCondition = leonToZ3.getZ3Expr(removeErrors(precondition))
    config = XConfig(solver, initialCondition, solverMaxIterMedium, solverPrecisionMedium)
  }

  val (minVal, maxVal) = precision.range
  val (maxNegNormal, minPosNormal) = (-precision.minNormal, precision.minNormal)
  /*val (machineEps, bits) = precision match {
    case FPPrecision(bts) => (Rational.zero, bts)
    case _ => (getUnitRoundoff(precision), 0)
  }*/

  private def getInitialVariables(in: VariablePool, exactInputs: Boolean,
    actualRanges: Boolean = false): Map[Expr, XReal] = precision match {
    
    case Float32 | Float64 | DoubleDouble | QuadDouble =>
      if (actualRanges && exactInputs) {
        variables2xfloatsActualExact(in.getValidInputRecords, config, precision)

      } else if (exactInputs) {
        // Only the method inputs are exact
        val inputVars: Map[Expr, XReal] = variables2xfloatsExact(in.getValidInputRecords, config, precision)
        val tmpVars: Map[Expr, XReal] = variables2xfloats(in.getValidTmpRecords, config, precision)._1
        inputVars ++ tmpVars
      }
      else if (in.integers.nonEmpty) {
        val (intRecords, rest) = in.getValidRecords.partition(
          rec => in.integers.contains(rec.idealId)
          )
        variables2xfloatsExact(intRecords, config, precision) ++
          variables2xfloats(rest, config, precision)._1
      } else {
        variables2xfloats(in.getValidRecords, config, precision)._1
      }

    case FPPrecision(bits) =>
      if (exactInputs) reporter.warning("no exact inputs for fixedpoint")
      variables2xfixed(in, config, bits)._1
  }



  /* Expects the expression to be open, i.e. to return a value
   * (as opposed to last expr being x == ...)
   *  Will work also for tupled results
   */
  def approximate(e: Expr, precond: Expr, inputs: VariablePool,
    exactInputs: Boolean = false): Seq[XReal] = {
    init(inputs, precond)
    val vars = getInitialVariables(inputs, exactInputs)
    process(e, vars, True)._3
  }

  def approximatePreinitialized(e: Expr, precond: Expr, inputs: VariablePool,
    variables: Map[Expr, XReal]): Seq[XReal] = {
    init(inputs, precond)
    val vars = variables
    process(e, vars, True)._3
  }

  def approximateEquations(e: Expr, precond: Expr, inputs: VariablePool,
    exactInputs: Boolean = false): Map[Expr, XReal] = {
    init(inputs, precond)
    val vars = getInitialVariables(inputs, exactInputs)
    val (newVars, path, res) = process(e, vars, True)
    //sanity check (does not hold for fixed-point code generation)
    //assert(res.length == 0, "computing xreals for equations but open expression found")
    // TODO: remove input vars?
    newVars
  }

  def approximateUpdateFncs(e: Expr, precond: Expr, inputs: VariablePool,
    exactInputs: Boolean = true, actualRanges: Boolean = true, updateFncs: Seq[Expr]): (Map[Expr, XReal], Seq[Rational]) = {
    init(inputs, precond)
    val vars = getInitialVariables(inputs, exactInputs, actualRanges)

    val (newVars, path, res) = process(e, vars, True)
    //sanity check
    assert(res.length == 0, "computing xreals for equations but open expression found")

    val sigmas = updateFncs.map(upfnc => {
      //println("trying to process: " + upfnc)
      //println("newVars: " + newVars)
      val res = process(upfnc, newVars, path)._3
      assert(res.length == 1)
      res(0).maxError
      })
    //println("sigmas: " + sigmas)
    // TODO: remove input vars?
    (newVars, sigmas)
  }

  // used for loops
  def computeError(e: Expr, precond: Expr, inputs: VariablePool,
    exactInputs: Boolean = false): Rational = e match {
    case BooleanLiteral(_) => Rational.zero
    case _ =>
      init(inputs, precond)
      val vars = getInitialVariables(inputs, exactInputs)
      println("vars: " + vars)
      val res = process(e, vars, True)._3
      assert(res.length == 1, "computing error on tuple-typed expression!")
      res(0).maxError
  }

  def computeErrorPreinitialized(e: Expr, precond: Expr, inputs: VariablePool,
    variables: Map[Expr, XReal]): Rational = e match {
    case BooleanLiteral(_) => Rational.zero
    case _ =>
      init(inputs, precond)
      val vars = variables
      val res = process(e, vars, True)._3
      assert(res.length == 1, "computing error on tuple-typed expression!")
      res(0).maxError
  }

  def computeErrorWithIntervals(e: Expr, precond: Expr, inputs: VariablePool,
    variables: Map[Expr, RationalInterval]): Rational = e match {
    case BooleanLiteral(_) => Rational.zero
    case _ =>
      init(inputs, precond)
      val vars: Map[Expr, XReal] = variables.map({
        case (v @ Variable(_), r @ RationalInterval(lo, hi)) =>
          (inputs.buddy(v), XFloat.xFloatExact(v, r, config, precision))
        })
      val res = process(e, vars, True)._3
      assert(res.length == 1, "computing error on tuple-typed expression!")
      res(0).maxError
  }

  // @return (path condition, result)
  def process(expr: Expr, vars: Map[Expr, XReal], path: Expr):
    (Map[Expr, XReal], Expr, Seq[XReal]) = expr match {
    case And(es) =>
      var currentPath: Expr = path
      var currentVars = vars
      var currRes: Option[Seq[XReal]] = None

      es.foreach { e =>
        val (newVars, newPath, res) = process(e, currentVars, currentPath)
        currentPath = newPath
        currentVars = newVars
        if (res.nonEmpty) {
          if (currRes.isEmpty) currRes = Some(res)
          else throw new Exception("Two results found in And expression")
        }
      }
      if (currRes.isEmpty)  (currentVars, currentPath, Seq())
      else (currentVars, currentPath, currRes.get)
      // first seq collects the path condition, second sequence collects the results
      /*val (path, allEs) = es.foldLeft((Seq[Expr](), Seq[XRealTuple]()))((counter, ex) => {
        ex match {
          case GreaterEquals(_, _) | GreaterThan(_, _) | LessEquals(_, _) | LessThan(_, _) =>
            (counter._1 :+ ex, counter._2)
          case _ =>
            (counter._1, counter._2 :+ approx(ex, counter._1))
        }
        })
      */
      //val allEs = for(ex <- es) yield approx(ex, path)
      //allEs.last

    // TODO: val (x1, x2) = fnc Call doesn't work atm
    case EqualsF(lhs, rhs) if (lhs.getType == RealType) =>
      val res = evalArithmetic(rhs, vars, path)

      //println("lhs: " + lhs)
      //val compactedRes = compactXFloat(res, inputVariables.getIdeal(lhs))
      //println("compactedRes: " + compactedRes)

      (vars + (lhs -> res), path, Seq())

    case EqualsF(lhs, rhs) =>
      throw new Exception("Cannot handle tupled Equals yet!")
      return (vars, path, Seq())

    case FloatIfExpr(cond, thenn, elze) =>
      //println("evaluating: " + expr)
      val currentPathCondition = And(path, initialCondition)
      val notCond = negate(cond)

      val thenBranch: Option[Seq[XReal]] =
        if (isFeasible(And(currentPathCondition, cond) )) {
          val (newVars, newPath, res) = process(thenn, vars, And(path, cond))
          Some(res)
        } else {
          None
        }
      //println("finished thenBranch: " + thenn)

      val elseBranch =
        if (isFeasible(And(currentPathCondition, notCond) )) {
          val (newVars, newPath, res) = process(elze, vars, And(path, notCond))
          Some(res)
        }
        else {
          None
        }
      //println("finished elseBranch: " + elze)

      val pathError: Seq[Rational] = if (checkPathError) {
        val pathError = new PathError(reporter, solver, precision, inputVariables, precondition, vars) 
        pathError.computePathErrors(currentPathCondition, cond, thenn, elze)

        //val pathError = new LipschitzPathError(reporter, solver, precision, inputVariables)
        //pathError.computePathErrors(precondition: Expr, branchCond: Expr, thenn, elze, vars)

      } else {
        Seq()
      }
      //println("pathError: " + pathError)

      (vars, path, mergeXReal(thenBranch, elseBranch, pathError, path))

    case FncBodyF(_, body, _, _) =>
      val (newVars, newPath, res) = process(body, vars, path)
      (vars, path, res)

    case Tuple(tpls) =>
      val result = tpls.map(tpl => {
        val (newVars, newPath, res) = process(tpl, vars, path)
        assert(res.length == 1, "tuple inside tuple found")
        res.head
        })
      (vars, path, result)

    case FncValueF(specs, specExpr) =>
      // TODO: we should filter out any non-real parts from the spec expression here
      //println("\nfncValueF: " + specs)
      //println("specExpr: " + specExpr)
      val res = specs.map (spec => {
        val (resId, interval, error, constraints) = (spec.id, spec.bounds, spec.absError.get, True) // constraints not (yet) used
        val fresh = getNewXFloatVar
        //println("fresh: " + fresh)
        precision match {
          case FPPrecision(bts) => xFixedWithUncertain(fresh, interval,
            config.addCondition(replace(Map(Variable(resId) -> fresh),
              leonToZ3.getZ3Condition(And(removeErrors(specExpr), spec.toRealExpr)))),
            error, false, bts)._1
        case _ => xFloatWithUncertain(fresh, interval,
          config.addCondition(replace(Map(Variable(resId) -> fresh),
            leonToZ3.getZ3Condition(And(removeErrors(specExpr), spec.toRealExpr)))),
          error, false, precision)._1
        }
      })
      (vars, path, res)

    case GreaterEquals(_, _) | GreaterThan(_, _) | LessEquals(_, _) | LessThan(_, _) =>
      (vars, And(path, expr), Seq())

    case x if (x.getType == RealType) =>
      val res = evalArithmetic(x, vars, path)
      (vars, path, Seq(res))

  }


  
  private def evalArithmetic(e: Expr, vars: Map[Expr, XReal], path: Expr): XReal = {
    if (useLipschitz) {
      //println("----> using lipschitz")
      //val lip = new Lipschitz(reporter, solver, leonToZ3)

      val currentVarsInExpr: Set[Identifier] = variablesOf(e)
      val varMap = vars.filter({case (Variable(id), _) => currentVarsInExpr.contains(id)}).map(
        x => (inputVariables.getIdeal(x._1), x._2))
      val ids = varMap.keys.map({ case Variable(id) => id}).toSeq
      val additionalConstraints = getRealConstraintClauses(precondition)

      val propagatedError = getPropagatedErrorLipschitz( Seq(actualToIdealArithmetic(e)),
        varMap, ids, additionalConstraints)
      //println("propagatedError: " + propagatedError)

      //println("vars before: " + vars)
      val varsWithoutErrors = vars.map({case (a, b) => (a, rmErrors(b))})
      //println("varsWithoutErrors: " + varsWithoutErrors)
      val roundoffError = approxArithm(e, varsWithoutErrors, path)
      //println("roundoffError: " + roundoffError)

      val newError = roundoffError.maxError + propagatedError.get(0)
      //println("new error: " + newError)
      val resNew = replaceError(roundoffError, newError)
      //println("resNew: " + resNew)
      resNew
    } else {  
      approxArithm(e, vars, path)
    }
  }

  private def getRealConstraintClauses(e: Expr): Expr = {
    And(getClauses(e).filter(cl => !belongsToActual(cl) && ! isRangeClause(cl)).toSeq)
  }


  private def approxArithm(e: Expr, vars: Map[Expr, XReal], path: Expr): XReal = {
    def getXRealWithCondition(v: Expr, cond: Expr): XReal = {
      v match {
        case v: Variable =>
          vars(v) match {
            case xfl: XFloat => new XFloat(xfl.tree, xfl.approxInterval, xfl.error, xfl.config.addCondition(leonToZ3.getZ3Condition(cond)), precision)
            case xfx: XFixed => new XFixed(xfx.format, xfx.tree, xfx.approxInterval, xfx.error, xfx.config.addCondition(leonToZ3.getZ3Condition(cond)))
          }

        case FloatLiteral(r) =>
          precision match {
            case FPPrecision(bits) => XFixed(r, config.addCondition(leonToZ3.getZ3Condition(cond)), bits)
            case _ => XFloat(r, config.addCondition(leonToZ3.getZ3Condition(cond)), precision) // TODO: save machineEps somewhere?
          }
      }
    }
    val tmp: XReal = e match {
      case UMinusF(t) =>        - approxArithm(t, vars, path)
      case PlusF(lhs, rhs) =>   approxArithm(lhs, vars, path) + approxArithm(rhs, vars, path)
      case MinusF(lhs, rhs) =>  approxArithm(lhs, vars, path) - approxArithm(rhs, vars, path)
      case TimesF(lhs, rhs) =>  approxArithm(lhs, vars, path) * approxArithm(rhs, vars, path)
      case DivisionF(lhs, rhs) =>
        val r = approxArithm(rhs, vars, path)
        if (possiblyZero(r.interval)) throw RealArithmeticException("Potential div-by-zero detected: " + e)
        approxArithm(lhs, vars, path) / r

      case SqrtF(t) =>
        val x = approxArithm(t, vars, path)
        if (possiblyNegative(x.interval)) throw RealArithmeticException("Potential sqrt of negative detected: " + e)
        x.squareRoot

      /*   Terminals */
      case fl: FloatLiteral => getXRealWithCondition(fl, path)
      case v: Variable => getXRealWithCondition(v, path)

      // only the case when we have a single value and not a tuple...
      case FncValueF(specs, specExpr) =>
        // TODO: we should filter out any non-real parts from the spec expression here
        //println("\nfncValueF: " + specs)
        //println("specExpr: " + specExpr)
        val res = specs.map (spec => {
          val (resId, interval, error, constraints) = (spec.id, spec.bounds, spec.absError.get, True) // constraints not (yet) used
          val fresh = getNewXFloatVar
          //println("fresh: " + fresh)
          precision match {
            case FPPrecision(bts) => xFixedWithUncertain(fresh, interval,
              config.addCondition(replace(Map(Variable(resId) -> fresh),
                leonToZ3.getZ3Condition(And(removeErrors(specExpr), spec.toRealExpr)))),
              error, false, bts)._1
          case _ => xFloatWithUncertain(fresh, interval,
            config.addCondition(replace(Map(Variable(resId) -> fresh),
              leonToZ3.getZ3Condition(And(removeErrors(specExpr), spec.toRealExpr)))),
            error, false, precision)._1
          }
        })
        assert(res.length == 1)
        res(0)

      case FncBodyF(_, body, _, _) =>
        val (newVars, newPath, res) = process(body, vars, path)
        assert(res.length == 1)
        res(0)
    }
    if (overflowPossible(tmp.interval)) {
      reporter.warning("Possible overflow detected at: " + tmp)
    }
    if (denormal(tmp.interval)) {
      throw RealArithmeticException("Denormal value detected for " + e)
    }

    if (formulaSize(tmp.tree) > compactingThreshold) {
      reporter.warning("compacting, size: " + formulaSize(tmp.tree))
      val fresh = getNewXFloatVar
      compactXFloat(tmp, fresh)
    } else {
      tmp
    }

  }//end approxArithm

  private def isFeasible(pre: Expr): Boolean = {
    import Sat._
    solver.checkSat(leonToZ3.getZ3Expr(pre)) match {
      case (SAT, model) => true
      case (UNSAT, model) => false
      case _ =>
        reporter.info("Sanity check failed! ")// + sanityCondition)
        false
    }
  }

  private def mergeXReal(one: Option[Seq[XReal]], two: Option[Seq[XReal]], pathErrors: Seq[Rational],
    condition: Expr): Seq[XReal] = (one, two) match {
    // We assume that one of the two branches is feasible
    case (None, None) =>
      throw new Exception("One of the paths should be feasible")
      null

    case (Some(seq1), None) =>
      if (pathErrors.nonEmpty) {
        seq1.zip(pathErrors).map({
          case (x1, pathError) =>
            val newError = max(x1.maxError, pathError)
            val newInt = x1.realInterval
            val fresh = getNewXFloatVar
            val newConfig = config.addCondition(leonToZ3.getZ3Condition(And(condition, rangeConstraint(fresh, newInt))))
            precision match {
              case FPPrecision(bts) => xFixedWithUncertain(fresh, newInt, newConfig, newError, false, bts)._1
              case _ => xFloatWithUncertain(fresh, newInt, newConfig, newError, false, precision)._1
            }
        })
      } else {
        seq1
      }
    case (None, Some(seq2)) =>
      if (pathErrors.nonEmpty) {
        seq2.zip(pathErrors).map({
          case (x2, pathError) =>
            val newError = max(x2.maxError, pathError)
            val newInt = x2.realInterval
            val fresh = getNewXFloatVar
            val newConfig = config.addCondition(leonToZ3.getZ3Condition(And(condition, rangeConstraint(fresh, newInt))))
            precision match {
              case FPPrecision(bts) => xFixedWithUncertain(fresh, newInt, newConfig, newError, false, bts)._1
              case _ => xFloatWithUncertain(fresh, newInt, newConfig, newError, false, precision)._1
            }
        })
      } else {
        seq2
      }

    case (Some(seq1), Some(seq2)) =>
      seq1.zip(seq2).zipWithIndex.map({
        case ((x1, x2), i) =>
          val pathError = pathErrors.applyOrElse(i, (j: Int) => Rational.zero)
          val newInt = x1.realInterval.union(x2.realInterval)
          val newError = max(max(x1.maxError, x2.maxError), pathError)
          val fresh = getNewXFloatVar
          val newConfig = config.addCondition(leonToZ3.getZ3Condition(And(condition, rangeConstraint(fresh, newInt))))
          precision match {
            case FPPrecision(bts) => xFixedWithUncertain(fresh, newInt, newConfig, newError, false, bts)._1
            case _ => xFloatWithUncertain(fresh, newInt, newConfig, newError, false, precision)._1
          }
      })
  }

  private def overflowPossible(interval: RationalInterval): Boolean = interval.xlo < minVal || maxVal < interval.xhi

  private def possiblyZero(interval: RationalInterval): Boolean = interval.xlo < Rational.zero && interval.xhi > Rational.zero

  private def possiblyNegative(interval: RationalInterval): Boolean = interval.xlo < Rational.zero || interval.xhi < Rational.zero

  // tests if the entire interval lies in the denormal range
  private def denormal(interval: RationalInterval): Boolean = precision match {
    case FPPrecision(_) => false
    case _ => (interval.xlo != interval.xhi && maxNegNormal < interval.xlo && interval.xhi < minPosNormal)
  }

  private def compactXFloat(xreal: XReal, newTree: Expr): XReal = {
    val newConfig = xreal.config.addCondition(rangeConstraint(newTree, xreal.realInterval))
    val (newXReal, index) = xreal match {
      case xf: XFloat =>
        xFloatWithUncertain(newTree, xreal.approxInterval, newConfig, xreal.maxError, false, xf.precision)
      case xfp: XFixed =>
        xFixedWithUncertain(newTree, xreal.approxInterval, newConfig, xreal.maxError, false, xfp.format.bits)
    }
    newXReal
  }

  private def actualToIdealArithmetic(expr: Expr): Expr = {
    preMap {
      case UMinusF(t) => Some(UMinusR(t))
      case PlusF(lhs, rhs) => Some(PlusR(lhs, rhs))
      case MinusF(lhs, rhs) => Some(MinusR(lhs, rhs))
      case TimesF(lhs, rhs) => Some(TimesR(lhs, rhs))
      case DivisionF(lhs, rhs) => Some(DivisionR(lhs, rhs))
      case SqrtF(t) => Some(SqrtR(t))
      case FloatLiteral(r) => Some(RealLiteral(r))
      case v @ Variable(_) => Some(inputVariables.getIdeal(v))
      
    }(expr)
  }

  // TODO: already exists in PathError
  private def rmErrors(xf: XReal): XReal = xf match {
    case xff: XFloat =>
      new XFloat(xff.tree, xff.approxInterval, new XRationalForm(Rational.zero), xff.config, xff.precision)
    case xfp: XFixed =>
      new XFixed(xfp.format, xfp.tree, xfp.approxInterval, new XRationalForm(Rational.zero), xfp.config)
  }

  private def replaceError(xf: XReal, newError: Rational): XReal = xf match {
    case xff: XFloat =>
      new XFloat(xff.tree, xff.approxInterval, new XRationalForm(newError), xff.config, xff.precision)
    case xfp: XFixed =>
      new XFixed(xfp.format, xfp.tree, xfp.approxInterval, new XRationalForm(newError), xfp.config)
  }

}