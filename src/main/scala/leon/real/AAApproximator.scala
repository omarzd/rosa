/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package real

import purescala.Trees._
import purescala.TypeTrees.{RealType, TupleType}
import purescala.TreeOps._
import purescala.Common._

import real.Trees._
import real.TreeOps._
import VariableShop._
import Rational.{max, zero}
import Precision._
import XNum.{records2xnums, records2xnumsExact, records2xnumsActualExact}

// Manages the approximation
class AAApproximator(val reporter: Reporter, val solver: RangeSolver, prec: Precision, val silent: Boolean, checkPathError: Boolean = true,
  useLipschitz: Boolean = false, collectIntervals: Boolean = false) extends Lipschitz {

  implicit override val debugSection = utils.DebugSectionAffine
  val compactingThreshold = 500

  implicit val precision: Precision = prec

  var leonToZ3: LeonToZ3Transformer = null
  var inputVariables: VariablePool = null
  var initialCondition: Expr = True  //precondition
  var additionalConstraints: Set[Expr] = Set()
  var precondition: Expr = True
  var fpIntervals: Map[Expr, RationalInterval] = Map()

  private def init(inputs: VariablePool, precond: Expr) = {
    inputVariables = inputs
    precondition = precond
    leonToZ3 = new LeonToZ3Transformer(inputs, precision)
    initialCondition = leonToZ3.getZ3Expr(removeErrors(precondition))
    fpIntervals = Map()
  }

  val (minVal, maxVal) = precision.range
  val (maxNegNormal, minPosNormal) = (-precision.minNormal, precision.minNormal)
  

  // @param exactInputs: do not add initial errors
  private def getInitialVariables(in: VariablePool, exactInputs: Boolean,
    actualRanges: Boolean = false): Map[Expr, XNum] = {

    if (actualRanges && exactInputs) records2xnumsActualExact(in.getValidInputRecords, initialCondition, Set())
    else if (exactInputs) {
      val inputVars = records2xnumsExact(in.getValidInputRecords, initialCondition, Set())
      val tmpVars = records2xnums(in.getValidTmpRecords, initialCondition, Set(), false)
      inputVars ++ tmpVars
    } else {
      records2xnums(in.getValidRecords, initialCondition, Set(), false)
    }
  
  }


  /* Expects the expression to be open, i.e. to return a value
   * (as opposed to last expr being x == ...)
   *  Will work also for tupled results
   */
  def approximate(e: Expr, precond: Expr, inputs: VariablePool,
    exactInputs: Boolean = false): Seq[XNum] = {
    init(inputs, precond)
    val vars = getInitialVariables(inputs, exactInputs)
    process(e, vars, True)._3
  }

  def approximatePreinitialized(e: Expr, precond: Expr, inputs: VariablePool,
    variables: Map[Expr, XNum]): Seq[XNum] = {
    init(inputs, precond)
    val vars = variables
    process(e, vars, True)._3
  }

  def approximateEquations(e: Expr, precond: Expr, inputs: VariablePool,
    exactInputs: Boolean = false): Map[Expr, XNum] = {
    init(inputs, precond)
    val vars = getInitialVariables(inputs, exactInputs)

    val start = System.currentTimeMillis
    val (newVars, path, res) = process(e, vars, True)
    reporter.info("approximateEquations, process: " + (System.currentTimeMillis - start))

    //sanity check (does not hold for fixed-point code generation)
    //assert(res.length == 0, "computing xreals for equations but open expression found")
    // TODO: remove input vars?
    newVars
  }

  // @ actualRanges: take the actual ranges instead of ideal ones for 
  // roundoff computation. Note that the precond also has to be adjusted!
  def approximateUpdateFncs(e: Expr, precond: Expr, inputs: VariablePool,
    exactInputs: Boolean = true, actualRanges: Boolean = true,
     updateFncs: Seq[Expr]): (Map[Expr, XNum], Seq[Rational]) = {
    
    init(inputs, precond)
    val vars = getInitialVariables(inputs, exactInputs, actualRanges)

    val (newVars, path, res) = process(e, vars, True)
    //sanity check
    assert(res.length == 0, "computing xreals for equations but open expression found")

    val sigmas = updateFncs.map(upfnc => {
      val res = process(upfnc, newVars, path)._3
      assert(res.length == 1)
      res(0).maxError
      })
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
    variables: Map[Expr, XNum]): Rational = e match {
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
      val vars: Map[Expr, XNum] = variables.map({
        case (v @ Variable(_), r @ RationalInterval(lo, hi)) =>
          (inputs.buddy(v), XNum(v, r, initialCondition, Set(), zero, false))
        })
      val res = process(e, vars, True)._3
      assert(res.length == 1, "computing error on tuple-typed expression!")
      res(0).maxError
  }

  // @return (path condition, result)
  def process(expr: Expr, vars: Map[Expr, XNum], path: Expr):
    (Map[Expr, XNum], Expr, Seq[XNum]) = expr match {
    case And(es) =>
      var currentPath: Expr = path
      var currentVars = vars
      var currRes: Option[Seq[XNum]] = None

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
      

    // TODO: val (x1, x2) = fnc Call doesn't work atm
    case EqualsF(lhs, rhs) if (lhs.getType == RealType) =>
      val res = evalArithmetic(rhs, vars, path)

      if (collectIntervals) fpIntervals = fpIntervals + (lhs -> res.interval)

      (vars + (lhs -> res), path, Seq())

    case EqualsF(Tuple(args), rhs) => //if (lhs.getType == TupleType) =>
      val ress = process(rhs, vars, path)._3
      val resMap = args.zip(ress).toMap
      
      if (collectIntervals) {
        fpIntervals = fpIntervals ++ resMap.mapValues( _.interval)
      }

      (vars ++ resMap, path, Seq())

    case FloatIfExpr(cond, thenn, elze) =>
      //println("evaluating: " + expr)
      val currentPathCondition = And(path, initialCondition)
      val notCond = negate(cond)

      val thenBranch: Option[Seq[XNum]] =
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

      } else {
        Seq()
      }
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

    case FncValueF(specs, specExpr, _, _) =>
      // TODO: we should filter out any non-real parts from the spec expression here
      //println("\nfncValueF: " + specs)
      //println("specExpr: " + specExpr)
      val res = specs.map (spec => {
        val (resId, interval, error, constraints) = (spec.id, spec.realBounds, spec.absError.get, True) // constraints not (yet) used
        val fresh = getNewXFloatVar
        //println("fresh: " + fresh)

        val newCondition = replace(Map(Variable(resId) -> fresh),
              leonToZ3.getZ3Condition(And(removeErrors(specExpr), spec.toRealExpr)))

        XNum(fresh, interval, initialCondition, Set(newCondition), error, false)
      })
      (vars, path, res)

    case GreaterEquals(_, _) | GreaterThan(_, _) | LessEquals(_, _) | LessThan(_, _) =>
      (vars, And(path, expr), Seq())

    case x if (x.getType == RealType) =>
      val res = evalArithmetic(x, vars, path)
      (vars, path, Seq(res))

  }


  
  private def evalArithmetic(e: Expr, vars: Map[Expr, XNum], path: Expr): XNum = {
    if (useLipschitz) {
      //println("----> using lipschitz")
      //val lip = new Lipschitz(reporter, solver, leonToZ3)

      val currentVarsInExpr: Set[Identifier] = variablesOf(e)
      val varMap = vars.filter({case (Variable(id), _) => currentVarsInExpr.contains(id)}).map(
        x => (inputVariables.getIdeal(x._1), x._2))
      val ids = varMap.keys.map({ case Variable(id) => id}).toSeq
      val additionalConstraints = getRealConstraintClauses(precondition)

      val start = System.currentTimeMillis
      val propagatedError = getPropagatedErrorLipschitz( Seq(actualToIdealArithmetic(e)),
        varMap, ids, additionalConstraints)
      reporter.info("Propagation error time: " + (System.currentTimeMillis - start))
      //println("propagatedError: " + propagatedError)

      //println("vars before: " + vars)
      val varsWithoutErrors = vars.map({case (a, b) => (a, XNum.removeErrors(b))})
      //println("varsWithoutErrors: " + varsWithoutErrors)
      val start2 = System.currentTimeMillis
      val roundoffError = approxArithm(e, varsWithoutErrors, path)
      reporter.info("Approx arithmetic time: " + (System.currentTimeMillis - start2))
      //println("roundoffError: " + roundoffError)

      val newError = roundoffError.maxError + propagatedError.get(0)
      //println("new error: " + newError)
      val resNew = XNum.replaceError(roundoffError, newError)
      //println("resNew: " + resNew)
      resNew
    } else {  
      approxArithm(e, vars, path)
    }
  }

  private def getRealConstraintClauses(e: Expr): Expr = {
    And(getClauses(e).filter(cl => !belongsToActual(cl) && ! isRangeClause(cl)).toSeq)
  }


  private def approxArithm(e: Expr, vars: Map[Expr, XNum], path: Expr): XNum = {
    def getXRealWithCondition(v: Expr, cond: Expr): XNum = {
      //println("matching: " + v + "  -> " + inputVariables.isLoopCounter(v) + "  lpcntr: " + inputVariables.loopCounter)

      v match {
        case v: Variable if (!vars.contains(v) && inputVariables.isLoopCounter(inputVariables.getIdeal(v))) =>
          // should only happen with fixed-points during codegen
          assert(precision.isInstanceOf[FPPrecision])
          val addCond = Set(leonToZ3.getZ3Condition(And(cond, Equals(v, RealLiteral(zero)))))
          XNum(v, RationalInterval(zero, zero), initialCondition, addCond, zero, false)


        case v: Variable =>
          vars(v).addCondition(leonToZ3.getZ3Condition(cond))

        case FloatLiteral(r) =>
          XNum(RealLiteral(r), RationalInterval(r, r), initialCondition, 
           Set(leonToZ3.getZ3Condition(cond)), zero, true)

        case IntLiteral(i) =>// only for codegen in fixed-points
          assert(precision.isInstanceOf[FPPrecision])
          XNum(RealLiteral(Rational(i)), RationalInterval(Rational(i), Rational(i)), initialCondition,
            Set(leonToZ3.getZ3Condition(cond)), zero, false)

      }
    }

    val tmp: XNum = e match {
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
      case FloatLiteral(_) | IntLiteral(_) => getXRealWithCondition(e, path)
      case v: Variable => getXRealWithCondition(v, path)

      // only the case when we have a single value and not a tuple...
      case FncValueF(specs, specExpr, _, _) =>
        // TODO: we should filter out any non-real parts from the spec expression here
        //println("\nfncValueF: " + specs)
        //println("specExpr: " + specExpr)
        val res = specs.map (spec => {
          val (resId, interval, error, constraints) = (spec.id, spec.realBounds, spec.absError.get, True) // constraints not (yet) used
          val fresh = getNewXFloatVar
          //println("fresh: " + fresh)
          val addCond = replace(Map(Variable(resId) -> fresh),
                leonToZ3.getZ3Condition(And(removeErrors(specExpr), spec.toRealExpr)))
          XNum(fresh, interval, initialCondition, Set(addCond), error, false)
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

    if (formulaSize(tmp.realRange.tree) > compactingThreshold) {
      reporter.warning("compacting, size: " + formulaSize(tmp.realRange.tree))
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

  private def mergeXReal(one: Option[Seq[XNum]], two: Option[Seq[XNum]], pathErrors: Seq[Rational],
    condition: Expr): Seq[XNum] = (one, two) match {
    // We assume that one of the two branches is feasible
    case (None, None) =>
      throw new Exception("One of the paths should be feasible")
      null

    case (Some(seq1), None) =>
      if (pathErrors.nonEmpty) {
        seq1.zip(pathErrors).map({
          case (x1, pathError) =>
            val newError = max(x1.maxError, pathError)
            val newInt = x1.realRange.interval
            val fresh = getNewXFloatVar
            val addCond = leonToZ3.getZ3Condition(And(condition, rangeConstraint(fresh, newInt)))
            
            XNum(fresh, newInt, initialCondition, Set(addCond), newError, false)
        })
      } else {
        seq1
      }
    case (None, Some(seq2)) =>
      if (pathErrors.nonEmpty) {
        seq2.zip(pathErrors).map({
          case (x2, pathError) =>
            val newError = max(x2.maxError, pathError)
            val newInt = x2.realRange.interval
            val fresh = getNewXFloatVar
            val addCond = leonToZ3.getZ3Condition(And(condition, rangeConstraint(fresh, newInt)))
            
            XNum(fresh, newInt, initialCondition, Set(addCond), newError, false)
        })
      } else {
        seq2
      }

    case (Some(seq1), Some(seq2)) =>
      seq1.zip(seq2).zipWithIndex.map({
        case ((x1, x2), i) =>
          val pathError = pathErrors.applyOrElse(i, (j: Int) => Rational.zero)
          val newInt = x1.realRange.interval.union(x2.realRange.interval)
          val newError = max(max(x1.maxError, x2.maxError), pathError)
          val fresh = getNewXFloatVar

          val addCond = leonToZ3.getZ3Condition(And(condition, rangeConstraint(fresh, newInt)))
          XNum(fresh, newInt, initialCondition, Set(addCond), newError, false)
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

  private def compactXFloat(xreal: XNum, newTree: Expr): XNum = {
    val newConfig = xreal.addCondition(rangeConstraint(newTree, xreal.realRange.interval))
    XNum(newTree, xreal.realRange.interval, initialCondition, 
      xreal.realRange.additionalConstr + rangeConstraint(newTree, xreal.realRange.interval),
      xreal.maxError, false
      )
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

}