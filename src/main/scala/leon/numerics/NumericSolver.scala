package leon
package numerics

import z3.scala._

import purescala.Common._
import purescala.Trees._
import purescala.TreeOps._
import purescala.Definitions._
import solvers.z3._
import solvers._
import Sat._

import ceres.common.{Rational, RationalInterval}
import Rational._

import scala.collection.immutable.HashMap

object NumericSolver {

  var verbose = false
  // Does not have much of an impact compared to other issues
  // TODO: This should probably be relative
  val precision = Rational.rationalFromReal(0.0001)
  val maxIterationsBinary = 20

}


class NumericSolver(context: LeonContext, prog: Program) extends UninterpretedZ3Solver(context) {
  import NumericSolver._

  override val name = "numeric solver"
  override val description = "Z3 solver with some numeric convenience methods"

  var verbose = false
  var printWarnings = true
  var diagnose = true
  var countTimeouts = 0

  override protected[leon] val z3cfg = new Z3Config(
    "MODEL" -> true,
    "TIMEOUT" -> 250,
    "TYPE_CHECK" -> true,
    "WELL_SORTED_CHECK" -> true
  )

  setProgram(prog)
  initZ3

  val solver = z3.mkSolver

  def push = {
    solver.push
    if (verbose) println("solver, pushed")
  }

  def pop = {
    solver.pop()
    if (verbose) println("solver, popped")
  }

  def getNumScopes: Int = {
    solver.getNumScopes
  }

  private var variables = Set[Identifier]()

  def assertCnstr(expr: Expr) = {
    variables ++= variablesOf(expr)
    val exprInZ3 = toZ3Formula(expr).get
    solver.assertCnstr(exprInZ3)
    if (verbose) println("Added constraint: " + exprInZ3)
  }

  /**
   * Checks the given expression for satisfiability.
   */
  def check(expr: Expr): (Sat, Z3Model) = {
    solver.push
    variables ++= variablesOf(expr)
    val cnstr = toZ3Formula(expr).get
    solver.assertCnstr(cnstr)
    val res: (Sat, Z3Model) = solver.check match {
      case Some(true) =>
        if (verbose) println("--> cond: SAT")
        val model = solver.getModel
        println("model: " + modelToMap(model, variables))
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
/*
  def tightenRange(tree: Expr, initialBound: RationalInterval): RationalInterval = tree match {
    // Nothing to do for constants
    case IntLiteral(v) => initialBound
    case RationalLiteral(v) => initialBound
    case FloatLiteral(v) => initialBound

    // Also nothing to do for variables
    case Variable(id) => initialBound

    case _ =>
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
        if (lowerBoundIsTight(exprInZ3, a)) a
        else getLowerBound(a, b, exprInZ3, 0)


      if (verbose) println("\n============Looking for upperbound")

      val newUpperBound =
        if (upperBoundIsTight(exprInZ3, b)) b
        else getUpperBound(a, b, exprInZ3, 0)

      printBoundsResult(checkBounds(exprInZ3, newLowerBound, newUpperBound), "final")
      RationalInterval(newLowerBound, newUpperBound)
  }

  private def checkBounds(tree: Z3AST, lowBound: Rational, upBound: Rational): (Sat, Sat, String) = {
    val resLow = checkLowerBound(tree, lowBound)
    val resUp = checkUpperBound(tree, upBound)
    val diagnoseString = resLow._2 + "\n" + resUp._2
    (resLow._1, resUp._1, diagnoseString)
  }


  // TODO: Invariant: the lower bound is always sound, and the upper bound not
  private def getLowerBound(a: Rational, b: Rational, exprInZ3: Z3AST, count: Int): Rational = {
    // Enclosure of bound is precise enough
    if (b-a < precision || count > maxIterationsBinary) {
      return a
    }
    else {
      if (verbose) {
        println(a + "      -    " +b)
        println("a: " + a.toFractionString)
        println("b: " + b.toFractionString)
      }
      val mid = a + (b - a) / Rational(2l)
      if (verbose) {
        println("mid: " + mid)
        println("mid: " + mid.toFractionString)
      }
      val res = checkLowerBound(exprInZ3, mid)

      if (verbose) println("checked lwr bound: " + mid + ", with result: " + res)

      res._1 match {
        case SAT => getLowerBound(a, mid, exprInZ3, count + 1)
        case UNSAT => getLowerBound(mid, b, exprInZ3, count + 1)
        case Unknown => // Return safe answer
          //reporter.warning("Stopping (lower bnd) at iteration " + count)
          return a
      }
    }
  }

  //TODO: Invariant the upper bound is always sound, the lower bnd not
  private def getUpperBound(a: Rational, b: Rational, exprInZ3: Z3AST, count: Int): Rational = {

    // Enclosure of bound is precise enough
    if (b-a < precision || count > maxIterationsBinary) {
      return b
    }
    else {
      val mid = a + (b - a) / Rational(2l)
      val res = checkUpperBound(exprInZ3, mid)

      if (verbose) {
        println("checked upp bound: " + mid + ", with result: " + res)
      }

      res._1 match {
        case SAT => getUpperBound(mid, b, exprInZ3, count + 1)
        case UNSAT => getUpperBound(a, mid, exprInZ3, count + 1)
        case Unknown => // Return safe answer
          //reporter.warning("Stopping (upper bnd) at iteration " + count)
          return b
      }
    }
  }

  // Checking constraints of bounds, the variables have already been added
  // to the solver.
  private def checkConstraint: Sat = {
    val resLower = solver.check

    resLower match {
      case Some(true) =>
        if (verbose) println("--> bound: SAT")
        SAT
      case Some(false) =>
        if (verbose) println("--> bound: UNSAT")
        UNSAT
      case None => if (printWarnings) println("!!! WARNING: Z3 SOLVER FAILED")
        countTimeouts = countTimeouts + 1
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


  private def lowerBoundIsTight(exprInZ3: Z3AST, bound: Rational): Boolean = {
    solver.push
    solver.assertCnstr(z3.mkLT(exprInZ3, z3.mkNumeral(getNumeralString(bound + precision), realSort)))

    if (verbose) println("checking if lower bound is tight: " + solver.getAssertions.toSeq.mkString(",\n"))

    val res = checkConstraint
    solver.pop()
    res match {
      case SAT => true
      case _ => false
    }
  }

  private def upperBoundIsTight(exprInZ3: Z3AST, bound: Rational): Boolean = {
    solver.push
    solver.assertCnstr(z3.mkGT(exprInZ3, z3.mkNumeral(getNumeralString(bound - precision), realSort)))

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

  // which: initial or final
  private def printBoundsResult(res: (Sat, Sat, String), which: String) = res match {
    case (SAT, SAT, msg) =>
      if (reporter != null)
        reporter.error("!!! ERROR: both " + which + " bounds are not sound!" +
          "\nmsg: " + msg + "\n ------------------")
      if (verbose) {
        println("!!! ERROR: both " + which + " bounds are not sound!" +
          "\nmsg: " + msg + "\n ------------------")
        throw new ArithmeticException("ouch")
      }
    case (SAT, _, msg) =>
      if (reporter != null)
        reporter.error("!!! ERROR: " + which + " lower bound is not sound!" +
          "\nmsg: " + msg + "\n ------------------")
      if (verbose) {
        println("!!! ERROR: " + which + " bounds are not sound!" +
          "\nmsg: " + msg + "\n ------------------")
        throw new ArithmeticException("ouch")
      }
    case (_, SAT, msg) =>
      if (reporter != null)
        reporter.error("!!! ERROR: " + which + " upper bound is not sound!" +
          "\nmsg: " + msg + "\n ------------------")
      if (verbose) {
        println("!!! ERROR: " + which + " bounds are not sound!" +
          "\nmsg: " + msg + "\n ------------------")
        throw new ArithmeticException("ouch")
      }
    case (UNSAT, UNSAT, msg) =>
      if (verbose) {
        println(which + " bounds check successful.")
      }
    case _ =>
      if (printWarnings) println("WARNING: cannot check "+which+" bounds.")
  }*/
}