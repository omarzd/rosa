/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import scala.collection.immutable.HashMap

import z3.{Z3Wrapper => Wrapper}
import z3.scala._

import purescala.Common._
import purescala.Trees.{Expr, Not, IntLiteral, Variable}
import purescala.TreeOps._
import purescala.Definitions._
import solvers.z3._
import solvers._

import real.TreeOps._
import real.Trees.RealLiteral
import Sat._
import Rational._

object RealSolver {
  var verbose = false
}

// TODO: This is not an ideal construction as we are duplicating everything in UninterpretedSolver,
// except the Z3Config, where we have to set the timeout.
class RealSolver(val context: LeonContext, val program: Program, timeout: Long)
  extends AbstractZ3Solver
     with Z3ModelReconstruction {

  import RealSolver._
  val name = "numeric solver"
  val description = "Z3 solver with some numeric convenience methods"

  //var verbose = false
  var printWarnings = false
  var diagnose = true
  var countTimeouts = 0
  var countTightRanges = 0
  var countHitPrecisionThreshold = 0
  var countHitIterationThreshold = 0

  def clearCounts = {
    countTimeouts = 0
    countTightRanges = 0
    countHitPrecisionThreshold = 0
    countHitIterationThreshold = 0
  }

  def getCounts: String = "timeouts: %d, tight: %d, hit precision: %d, hit iteration: %d".format(
    countTimeouts, countTightRanges, countHitPrecisionThreshold, countHitIterationThreshold)

  // this is fixed
  protected[leon] val z3cfg = new Z3Config(
    "MODEL" -> true,
    "TIMEOUT" -> timeout,
    "TYPE_CHECK" -> true,
    "WELL_SORTED_CHECK" -> true
  )

  toggleWarningMessages(true)

  // what the superclasses require
  private var functionMap: Map[FunDef, Z3FuncDecl] = Map.empty
  private var reverseFunctionMap: Map[Z3FuncDecl, FunDef] = Map.empty
  protected[leon] def prepareFunctions : Unit = {
    functionMap        = Map.empty
    reverseFunctionMap = Map.empty
    for(funDef <- program.definedFunctions) {
      val sortSeq = funDef.args.map(vd => typeToSort(vd.tpe))
      val returnSort = typeToSort(funDef.returnType)

      val z3Decl = z3.mkFreshFuncDecl(funDef.id.name, sortSeq, returnSort)
      functionMap = functionMap + (funDef -> z3Decl)
      reverseFunctionMap = reverseFunctionMap + (z3Decl -> funDef)
    }
  }
  protected[leon] def functionDefToDecl(funDef: FunDef) : Z3FuncDecl = functionMap(funDef)
  protected[leon] def functionDeclToDef(decl: Z3FuncDecl) : FunDef = reverseFunctionMap(decl)
  protected[leon] def isKnownDecl(decl: Z3FuncDecl) : Boolean = reverseFunctionMap.isDefinedAt(decl)

  initZ3

  //z3.enableTrace("nlarith")
  //Wrapper.openLog("z3Log.txt")

  val solver = z3.mkSolver

  def getNumScopes: Int = {
    solver.getNumScopes
  }

  def push() {
    solver.push
  }


  def pop(lvl: Int = 1) {
    solver.pop(lvl)
  }

  private var variables = Set[Identifier]()
  private var containsFunCalls = false

  def assertCnstr(expression: Expr) {
    variables ++= variablesOf(expression)
    containsFunCalls ||= containsFunctionCalls(expression)
    solver.assertCnstr(toZ3Formula(expression).get)
  }

  def innerCheck: Option[Boolean] = {
    solver.check match {
      case Some(true) =>
        if (containsFunCalls) {
          None
        } else {
          Some(true)
        }

      case r =>
        r
    }
  }

  def innerCheckAssumptions(assumptions: Set[Expr]): Option[Boolean] = {
    variables ++= assumptions.flatMap(variablesOf(_))
    solver.checkAssumptions(assumptions.toSeq.map(toZ3Formula(_).get) : _*)
  }

  def getModel = {
    modelToMap(solver.getModel, variables)
  }

  def getUnsatCore = {
    solver.getUnsatCore.map(ast => fromZ3Formula(null, ast, None) match {
      case n @ Not(Variable(_)) => n
      case v @ Variable(_) => v
      case x => scala.sys.error("Impossible element extracted from core: " + ast + " (as Leon tree : " + x + ")")
    }).toSet
  }

  // TODO: check if we need this is in the first place
  /*override def assertCnstr(expr: Expr) = {
    val exprInZ3 = toZ3Formula(expr).get
    solver.assertCnstr(exprInZ3)
    if (verbose) println("Added constraint: " + exprInZ3)
  }*/


  // Our stuff
  
  def checkSat(expr: Expr): (Sat, Z3Model) = {
    solver.push
    val variables = variablesOf(expr)
    val cnstr = toZ3Formula(expr)
    solver.assertCnstr(cnstr.get)
    val res: (Sat, Z3Model) = solver.check match {
      case Some(true) =>
        if (verbose) println("--> cond: SAT")
        val model = solver.getModel
        //println("model: " + modelToMap(model, variables))
        (SAT, solver.getModel)
      case Some(false) =>
        if (verbose) println("--> cond: UNSAT")
        (UNSAT, null)
      case None =>
        if (printWarnings) println("!!! WARNING: Z3 SOLVER FAILED")
        countTimeouts = countTimeouts + 1
        (Unknown, null)
    }
    solver.pop()
    res
  }


  def checkValid(expr: Expr): (Option[Boolean], Option[Map[Identifier, Expr]]) = {
    solver.push
    val variables = variablesOf(expr)
    val cnstr = toZ3Formula(Not(expr)).get
    //println("asserting constraint: " + cnstr)
    solver.assertCnstr(cnstr)
    val res = solver.check match {
      case Some(true) =>
        if (verbose) println("--> cond: SAT")
        val model = solver.getModel
        (Some(false), Some(modelToMap(model, variables)))
      case Some(false) =>
        if (verbose) println("--> cond: UNSAT")
        (Some(true), None)
      case None =>
        if (printWarnings) println("!!! WARNING: Z3 SOLVER FAILED")
        countTimeouts = countTimeouts + 1
        (None, None)
    }
    solver.pop()
    res
  }

  // Just so we have it
  def getRange(precond: Expr, expr: Expr, variables: VariablePool, maxIter: Int, prec: Rational) = {
    val approx = inIntervals(expr, variables)
    tightenRange(massageArithmetic(expr), precond, approx, maxIter, prec)
  }

  def tightenRange(tree: Expr, precondition: Expr, initialBound: RationalInterval, maxIter: Int, prec: Rational):
    RationalInterval = tree match {
    case IntLiteral(v) => initialBound
    case RealLiteral(v) => initialBound
    //case Variable(id) => initialBound
    case _ =>
      //println("maxIter: " + maxIter + "    precision: " + prec)
      assert(solver.getNumScopes == 0)
      solver.push
      assertCnstr(precondition)

      val a = initialBound.xlo
      val b = initialBound.xhi
      val exprInZ3 = toZ3Formula(tree).get

      printBoundsResult(checkBounds(exprInZ3, a, b), "initial")

      if (verbose) {
        println("\nComputing range for " + tree)
        println("starting from  [" + a + ", " + b + "]")
        println("\n============Looking for lowerbound")
      }
      // Check if bound is already tight, if so don't bother running Z3 search
      val newLowerBound =
        if (lowerBoundIsTight(exprInZ3, a, prec)) {
          countTightRanges += 1
          a
        } else getLowerBound(a, b, exprInZ3, 0, maxIter, prec)

      if (verbose) println("\n============Looking for upperbound")
      //TODO: we could actually start searching from the newLowerBound, no?
      val newUpperBound =
        if (upperBoundIsTight(exprInZ3, b, prec)) {
          countTightRanges += 1
          b
        }
        else getUpperBound(a, b, exprInZ3, 0, maxIter, prec)

      printBoundsResult(checkBounds(exprInZ3, newLowerBound, newUpperBound), "final")

      solver.pop()
      RationalInterval(newLowerBound, newUpperBound)
  }

  private def checkBounds(tree: Z3AST, lowBound: Rational, upBound: Rational): (Sat, Sat, String) = {
    val resLow = checkLowerBound(tree, lowBound)
    val resUp = checkUpperBound(tree, upBound)
    val diagnoseString = resLow._2 + "\n" + resUp._2
    (resLow._1, resUp._1, diagnoseString)
  }


  private def getLowerBound(a: Rational, b: Rational, exprInZ3: Z3AST, count: Int, maxIter: Int, prec: Rational): Rational = {
    // Enclosure of bound is precise enough
    if (b-a < prec) {
      countHitPrecisionThreshold += 1
      return a
    } else if (count > maxIter) {
      countHitIterationThreshold += 1
      return a
    } else {
      val mid = a + (b - a) / Rational(2l)
      val res = checkLowerBound(exprInZ3, mid)

      if (verbose) println("checked lwr bound: " + mid + ", with result: " + res)

      res._1 match {
        case SAT => getLowerBound(a, mid, exprInZ3, count + 1, maxIter, prec)
        case UNSAT => getLowerBound(mid, b, exprInZ3, count + 1, maxIter, prec)
        case Unknown => // Return safe answer
          return a
      }
    }
  }

  private def getUpperBound(a: Rational, b: Rational, exprInZ3: Z3AST, count: Int, maxIter: Int, prec: Rational): Rational = {
    // Enclosure of bound is precise enough
    if (b-a < prec) {
      countHitPrecisionThreshold += 1
      return b
    } else if (count > maxIter) {
      countHitIterationThreshold += 1
      return b
    } else {
      val mid = a + (b - a) / Rational(2l)
      val res = checkUpperBound(exprInZ3, mid)

      if (verbose) println("checked upp bound: " + mid + ", with result: " + res)

      res._1 match {
        case SAT => getUpperBound(mid, b, exprInZ3, count + 1, maxIter, prec)
        case UNSAT => getUpperBound(a, mid, exprInZ3, count + 1, maxIter, prec)
        case Unknown => // Return safe answer
          return b
      }
    }
  }

  private def checkConstraint: Sat = {
    solver.check match {
      case Some(true) =>
        if (verbose) println("--> bound: SAT")
        SAT
      case Some(false) =>
        if (verbose) println("--> bound: UNSAT")
        UNSAT
      case None =>
        if (printWarnings) println("!!! WARNING: Z3 SOLVER FAILED")
        countTimeouts += 1
        Unknown
    }
  }

  private def checkLowerBound(exprInZ3: Z3AST, bound: Rational): (Sat, String) = {
    var diagnoseString = ""
    solver.push
    solver.assertCnstr(z3.mkLT(exprInZ3, z3.mkNumeral(getNumeralString(bound), realSort)))

    if (verbose) println("checking: " + solver.getAssertions.toSeq.mkString(",\n"))
    if (diagnose) diagnoseString += ("L: checking: " + solver.getAssertions.toSeq.mkString(",\n"))

    val res = checkConstraint
    solver.pop()
    (res, diagnoseString)
  }

  private def checkUpperBound(exprInZ3: Z3AST, bound: Rational): (Sat, String) = {
    var diagnoseString = ""
    solver.push
    solver.assertCnstr(z3.mkGT(exprInZ3, z3.mkNumeral(getNumeralString(bound), realSort)))

    if (verbose) println("checking: " + solver.getAssertions.toSeq.mkString(",\n"))
    if (diagnose) diagnoseString += ("U: checking: " + solver.getAssertions.toSeq.mkString(",\n"))

    val res = checkConstraint
    solver.pop()
    (res, diagnoseString)
  }


  private def lowerBoundIsTight(exprInZ3: Z3AST, bound: Rational, prec: Rational): Boolean = {
    // TODO: we're using push and pop, which prevents nlsat to be used, probably
    solver.push
    solver.assertCnstr(z3.mkLT(exprInZ3, z3.mkNumeral(getNumeralString(bound + prec), realSort)))
    if (verbose) println("checking if lower bound is tight: " + solver.getAssertions.toSeq.mkString(",\n"))
    val res = checkConstraint
    solver.pop()
    res match {
      case SAT => true
      case _ => false
    }
  }

  private def upperBoundIsTight(exprInZ3: Z3AST, bound: Rational, prec: Rational): Boolean = {
    solver.push
    solver.assertCnstr(z3.mkGT(exprInZ3, z3.mkNumeral(getNumeralString(bound - prec), realSort)))
    if (verbose) println("checking: " + solver.getAssertions.toSeq.mkString(",\n"))
    val res = checkConstraint
    solver.pop()
    res match {
      case SAT => true
      case _ => false
    }
  }

  private def getNumeralString(r: Rational): String = {
    r.n.toString + "/" + r.d.toString
  }

  // @param which: initial or final
  private def printBoundsResult(res: (Sat, Sat, String), which: String) = res match {
    case (SAT, SAT, msg) =>
      throw new UnsoundBoundsException("!!! ERROR: both " + which + " bounds are not sound!\nmsg: " + msg)
    case (SAT, _, msg) =>
      throw new UnsoundBoundsException("!!! ERROR: " + which + " lower bound is not sound!\nmsg: " + msg)
    case (_, SAT, msg) =>
      throw new UnsoundBoundsException("!!! ERROR: " + which + " upper bound is not sound!\nmsg: " + msg)
    case (UNSAT, UNSAT, msg) =>
      if (verbose) println(which + " bounds check successful.")
    case _ =>
      if (printWarnings || verbose) println("WARNING: cannot check "+which+" bounds.")
  }
}
