/* Copyright 2013 EPFL, Lausanne */

package leon
package real


import purescala.Trees._
import purescala.Common._
import purescala.TreeOps.{variablesOf, negate, replace}

import real.Trees._
import real.VariableShop._
import real.TreeOps.{idealToActual}
import Rational.{max, abs}

// Computes the path error
class PathError(reporter: Reporter, solver: RangeSolver, precision: Precision, machineEps: Rational,
  verbose: Boolean = false, inputs: VariablePool, vars: Map[Expr, XReal]) {

  implicit val debugSection = utils.DebugSectionAffine
  val approximator = new AAAproximator(reporter, solver, precision, checkPathError = true)

  var variables = vars
  val leonToZ3 = new LeonToZ3Transformer(inputs, precision)

  type XRealTuple = Seq[XReal]

  def computePathErrors(currentPathCondition: Expr, branchCond: Expr, thenn: Expr, elze: Expr): Seq[Rational] = {
    val pathError1 = computePathError(currentPathCondition, branchCond, thenn, elze)
    reporter.info("computed error 1: " + pathError1)

    // TODO: shouldn't this be NOT (branchCond) ???
    val pathError2 = computePathError(currentPathCondition, branchCond, elze, thenn)
    reporter.info("computed error 2: " + pathError1)

    pathError1.zip(pathError2).map({
      case (p1, p2) => max(p1, p2)
      })
  }

  // the float condition is to be used with the negation of the actual condition to get only
  // the values that are off-path
  def getOffPathConditions(cond: Expr, path: Expr): (Expr, Expr) = {
    def getTotalError(l: Expr, r: Expr): Expr = {
      val lActual = idealToActual(l, inputs)
      val rActual = idealToActual(r, inputs)

      val errLeft = approximator.process(lActual, variables, path)._3.head.maxError  //approx(lActual, path).head.maxError
      val errRight = approximator.process(rActual, variables, path)._3.head.maxError //approx(rActual, path).head.maxError
      RealLiteral(errLeft + errRight)
    }

    cond match {
      case LessThan(l, r) =>
        val totalError = getTotalError(l, r)
        val floatCond = LessThan(l, PlusR(r, totalError))
        val realCond = GreaterEquals(l, MinusR(r, totalError))
        (floatCond, realCond)

      case LessEquals(l, r) =>
        val totalError = getTotalError(l, r)
        val floatCond = LessEquals(l, PlusR(r, totalError))
        val realCond = GreaterThan(l, MinusR(r, totalError))
        (floatCond, realCond)

      case GreaterThan(l, r) =>
        val totalError = getTotalError(l, r)
        val floatCond = GreaterThan(l, MinusR(r, totalError))
        val realCond = LessEquals(l, PlusR(r, totalError))
        (floatCond, realCond)

      case GreaterEquals(l, r) =>
        val totalError = getTotalError(l, r)
        val floatCond = GreaterEquals(l, MinusR(r, totalError))
        val realCond = LessThan(l, PlusR(r, totalError))
        (floatCond, realCond)
    }
  }// end getOffPathConditions

  // Computes the path error for one direction and branch
  //@param branchCondition real-valued
  //@param f1 path to be taken by ideal execution
  //@param f2 path to be taken by floating-point execution
  def computePathError(currentPathCondition: Expr, branchCondition: Expr, f1: Expr, f2: Expr): Seq[Rational] = {
    def rmErrors(xf: XReal): XReal = xf match {
      case xff: XFloat =>
        new XFloat(xff.tree, xff.approxInterval, new XRationalForm(Rational.zero), xff.config, xff.machineEps)
      case xfp: XFixed =>
        new XFixed(xfp.format, xfp.tree, xfp.approxInterval, new XRationalForm(Rational.zero), xfp.config)
    }
    def removeErrors(xfs: XRealTuple): XRealTuple = xfs.map(x => rmErrors(x))

    def addCondToXReal(xf: XReal, condition: Expr): XReal = xf match {
      case xff: XFloat =>
        new XFloat(xff.tree, xff.approxInterval, xff.error, xff.config.addCondition(condition), xff.machineEps)
      case xfp: XFixed =>
        new XFixed(xfp.format, xfp.tree, xfp.approxInterval, xfp.error, xfp.config.addCondition(condition))
    }
    def addConditionToXReal(xfs: XRealTuple, condition: Expr): XRealTuple =
      xfs.map(x => addCondToXReal(x, condition))

    if (verbose) println("--------\n computing path error for condition: " + branchCondition)
    if (verbose) println("real path: "+ f1)
    if (verbose) println("actual path: "+f2)

    //([c], errc) = evalWithError(pre, c)
    val (flCond, reCond) = getOffPathConditions(branchCondition, currentPathCondition)

    val floatCondition = And(flCond, negate(branchCondition))
    val realCondition = And(reCond, branchCondition)
    if (verbose) println("floatCondition: %s\nrealCondition: %s".format(floatCondition, realCondition))

    //println("----> feasible? " + isFeasible(Seq(initialCondition, floatCondition)))
    //println(isFeasible(Seq(initialCondition, realCondition)))

    if (isFeasible(And(currentPathCondition, floatCondition)) && isFeasible(And(currentPathCondition, realCondition))) {

      val variablesOfPaths = variablesOf(f1) ++ variablesOf(f2)

      //[f1]real = getRange(pre ∧ c(x) ∈ [−errc, 0], f1)
      val (freshMapReal, inputs1) = getFreshVariablesWithConditionWithoutErrors(variablesOfPaths, realCondition)
      if (verbose) println("freshMapReal: " + freshMapReal + "\ninputs1:")
      if (verbose) inputs1.foreach{ i => println(i.toString + " " + i._2.config)}

      variables = variables ++ inputs1
      solver.clearCounts
      //XFloat.verbose = true
      // don't add the branchCondition to the path, since it's in terms of real variables and will cause an invalid result
      // the branchCondition is already added to the config of the variables, and for constants it doesn't matter
      //println("realPath: " + replace(freshMapReal, f1))
      val realResult = approximator.process(replace(freshMapReal, f1), variables, currentPathCondition)._3  //approx(replace(freshMapReal, f1), path)
      //println("real result config: " + realResult.config.getCondition)
      //println("real result: " + realResult)
      //println("solverPrecision: " + realResult.config.solverPrecision)
      if (verbose) println("realResult: " + removeErrors(realResult))


      //([f2]float, errfloat) = evalWithError(pre ∧ c(x) ∈ [0, errc], f2)
      //(Map[Expr, Expr], Map[Expr, XFloat])
      val (freshMapFloat, inputs2) = getFreshVariablesWithConditionWithoutErrors(variablesOfPaths, floatCondition)
      if (verbose) println("freshMapFloat: " + freshMapFloat + "\ninputs2: ")
      //if (verbose) inputs2.foreach{ i => println(i.toString + " " + i._2.config) }

      variables = variables ++ inputs2
      solver.clearCounts
      val floatResult = approximator.process(replace(freshMapFloat, f2), variables, currentPathCondition)._3 //approx(replace(freshMapFloat, f2), path)
      //println("floatResult: " + floatResult)


      //return: max |[f1]real − ([f2]float + errfloat)|
      val correlation = variables.filter { x => x._1 match {
            case Variable(id) => variablesOfPaths.contains(id)
            case _ => false
          }}.map {
        case (v, xf) =>
          val freshErrorVar = getNewErrorVar
          And(Seq(Equals(freshMapFloat(v), PlusR(freshMapReal(v), freshErrorVar)),
          LessEquals(RealLiteral(-xf.maxError), freshErrorVar),
          LessEquals(freshErrorVar, RealLiteral(xf.maxError))))
        }
      if (verbose) println("correlation: " + correlation)

      val realResultWithCorrelation = addConditionToXReal(removeErrors(realResult), And(correlation.toSeq))
        //new XFloat(realResult.tree, realResult.approxInterval, new XRationalForm(Rational.zero),
        //realResult.config.addCondition(And(correlation.toSeq)))
      if (verbose) println("realResultWithCorrelation: " + realResultWithCorrelation)
      //println("\n realRangeWithCorrelation.config" + realResultWithCorrelation.config.getCondition)

      //println("floatResult.config: " + floatResult.config.getCondition)
      solver.clearCounts
      //XFloat.verbose = true
      //val diffXFloat = (floatResult - realResultWithCorrelation)
      val diffXFloat: XRealTuple = floatResult.zip(realResultWithCorrelation).map({
        case (fl, re) => fl - re
        })
      val diff: Seq[RationalInterval] = diffXFloat.map(_.interval)
      if (verbose) println("diff: " + diff)
      //println("diff config: " + diffXFloat.config.getCondition)
      if (verbose) reporter.info("STATS for diff: " + solver.getCounts)
      //XFloat.verbose = false
      // restore state from before
      variables = variables -- inputs1.keys -- inputs2.keys
      //XFloat.verbose = false
      val maxError: Seq[Rational] = diff.map(d => max(abs(d.xlo), abs(d.xhi)))
      if (verbose) println("maxError: " + maxError)
      maxError

    } else {
      reporter.debug("Other path not feasible")
      Seq()
    }
  }

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

  private def getFreshVariablesWithConditionWithoutErrors(vars: Set[Identifier], cond: Expr): (Map[Expr, Expr], Map[Expr, XReal]) = {
    var freshMap: Map[Expr, Expr] = variables.collect {
      case (v @ Variable(id), xf) if (vars.contains(id)) => (v, getFreshVarOf(id.toString))
    }
    //ideal to new variables
    var buddyFreshMap: Map[Expr, Expr] = variables.collect {
      case (v @ Variable(id), xf) if (vars.contains(id)) => (inputs.getIdeal(v), freshMap(v))
    }

    val newInputs =
      freshMap.map {
      case (v, fresh) =>
        val xf = variables(v)
        // TODO: add condition before to improve the approx interval?
        precision match {
          case FPPrecision(bits) =>
            (fresh, new XFixed(xf.asInstanceOf[XFixed].format, replace(buddyFreshMap, xf.tree), xf.approxInterval, new XRationalForm(Rational.zero),
              xf.config.addCondition(cond).freshenUp(buddyFreshMap).updatePrecision(solverMaxIterHigh, solverPrecisionHigh)))

          case _ =>
            (fresh, new XFloat(replace(buddyFreshMap, xf.tree), xf.approxInterval, new XRationalForm(Rational.zero),
              xf.config.addCondition(cond).freshenUp(buddyFreshMap).updatePrecision(solverMaxIterHigh, solverPrecisionHigh), machineEps))
        }
    }
    (freshMap, newInputs)
  }
}