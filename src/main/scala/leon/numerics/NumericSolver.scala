package leon
package numerics

import ceres.common.{Rational, RationalInterval}
import Rational._

import z3.scala._
import scala.collection.immutable.HashMap
import Sat._

import purescala.Trees._
import purescala.Definitions._
import solvers.z3._
import solvers._

object NumericSolver {

}


/* TODO:
   - make this break if z3 has wrong version.
   - conversion from BigInt to Int not safe when constructing expression
      (the code for that is now in solver.z3.AbstractZ3Solver) 
 */

// keeps only one Z3 solver around
// extending the uninterpreted solver takes care of the functionmap related details
class NumericSolver(context: LeonContext, prog: Program) extends UninterpretedZ3Solver(context) {
  override val name = "numeric solver"
  override val description = "Z3 solver with some numeric convenience methods"

  var verbose = false
  var diagnose = true

  override protected[leon] val z3cfg = new Z3Config(
    "MODEL" -> true,
    "TIMEOUT" -> 500,
    "TYPE_CHECK" -> true,
    "WELL_SORTED_CHECK" -> true
  )

  setProgram(prog)
  initZ3

  var solver = z3.mkSolver

  /*override def initZ3() {
    super.initZ3
    //realSort = z3.mkRealSort
    solver = z3.mkSolver
  }*/

  var variables: Map[Variable, Z3AST] = Map.empty

  // TODO this can be done differently

  // one way, we can't remove them again
  def addVariables(varConstraints: Map[Variable, RationalInterval]) = {
    val newVars: Map[Variable, Z3AST] = varConstraints.map(s =>
      (s._1, z3.mkFreshConst(s._1.id.name, realSort))
    )
    variables = variables ++ newVars
    if (verbose) { 
      println("Added new variables: " + newVars)
      println("New var map: " + variables)
    }

    val intRanges = varConstraints.map( s =>
      (s._1, RationalInterval(scaleToIntsDown(s._2.xlo), scaleToIntsUp(s._2.xhi)))
    )
    if (verbose) println("ranges:    " + varConstraints)
    if (verbose) println("intRanges: " + intRanges)
    // We need to approximate the BigRational to Rational
    val boundsList: Map[Variable, Z3AST] = varConstraints.map(s =>
      (s._1, z3.mkAnd(z3.mkGE(variables(s._1),
          z3.mkReal(intRanges(s._1).xlo.n.toInt, intRanges(s._1).xlo.d.toInt)),
        z3.mkLE(variables(s._1),
          z3.mkReal(intRanges(s._1).xhi.n.toInt, intRanges(s._1).xhi.d.toInt))))
    )
 
    val boundsInZ3: Z3AST = boundsList.foldLeft(z3.mkTrue)(
        (a, m) => z3.mkAnd(a, m._2))
    if (verbose) println("bounds: " + boundsInZ3)

    solver.assertCnstr(boundsInZ3)
  }

  //this should replace the call addVariables at some point
  def assertCnstr(expr: Expr) = {
    val exprInZ3 = toZ3Formula(expr).get
    solver.assertCnstr(exprInZ3)
  }

  def push = {
    solver.push
  }

  def pop = {
    solver.pop(1)
  }

  def checkLowerBound(expr: Expr, bound: Rational): (Sat, String) = {
    val exprInZ3 = toZ3Formula(expr).get //exprToz3(expr, variables)
    val boundMin = scaleToIntsDown(bound)
    var diagnoseString = ""
   
    solver.push
    solver.assertCnstr(z3.mkLT(exprInZ3, z3.mkReal(boundMin.n.toInt, boundMin.d.toInt)))

    if (verbose) println("checking: " + solver.getAssertions.toSeq.mkString(",\n"))
    if (diagnose) diagnoseString += ("L: checking: " + solver.getAssertions.toSeq.mkString(",\n"))


    val resLower = solver.check
   
    val res = resLower match {
      case Some(true) =>
        if (verbose) println("--> lower bound: SAT")
        SAT
      case Some(false) =>
        if (verbose) println("--> lower bound: UNSAT")
        UNSAT
      case None => println("!!! WARNING: Z3 SOLVER FAILED")
        Unknown
    }
    solver.pop(1)
    (res, diagnoseString)
  }

  def checkUpperBound(expr: Expr, bound: Rational): (Sat, String) = {
    val exprInZ3 = toZ3Formula(expr).get //exprToz3(expr, variables)
    val boundMax = scaleToIntsUp(bound)
    var diagnoseString = ""

    solver.push
    solver.assertCnstr(z3.mkGT(exprInZ3, z3.mkReal(boundMax.n.toInt, boundMax.d.toInt)))

    if (verbose) println("checking: " + solver.getAssertions.toSeq.mkString(",\n"))
    if (diagnose) diagnoseString += ("U: checking: " + solver.getAssertions.toSeq.mkString(",\n"))

    val resUpper = solver.check
    
    val res = resUpper match {
      case Some(true) =>
        if (verbose) println("--> upper bound: SAT")
        SAT
      case Some(false) =>
        if (verbose) println("--> upper bound: UNSAT")
        UNSAT
      case None => println("!!! WARNING: Z3 SOLVER FAILED")
        Unknown
    }
    solver.pop(1)
    (res, diagnoseString)
  }


  def check(expr: Expr): Sat = {
    solver.push
    val cnstr = toZ3Formula(expr).get //exprToz3(expr, Map.empty)
    solver.assertCnstr(cnstr)
    val res = solver.check match {
      case Some(true) =>
        if (verbose) println("--> cond: SAT")
        SAT
      case Some(false) =>
        if (verbose) println("--> cond: UNSAT")
        UNSAT
      case None =>
        println("!!! WARNING: Z3 SOLVER FAILED")
        Unknown
    }
    solver.pop(1)
    res
  }


  // TODO: conversion from BigInt to Int not safe
  /*private def exprToz3(expr: Expr, varMap: Map[Variable, Z3AST]): Z3AST = expr match {
    case RationalLiteral(v) =>
      // Not sound
      val c = scaleToIntsDown(v)
      println("n: " + v.n)
      println(v.n.toInt)
      println("d: " + v.d)
      println(v.d.toInt)
      z3.mkReal(c.n.toInt, c.d.toInt)
    case v @ Variable(id) => varMap(v)
    case FUMinus(rhs) => z3.mkUnaryMinus(exprToz3(rhs, varMap))
    case FPlus(lhs, rhs) => z3.mkAdd(exprToz3(lhs, varMap), exprToz3(rhs, varMap))
    case FMinus(lhs, rhs) => z3.mkSub(exprToz3(lhs, varMap), exprToz3(rhs, varMap))
    case FTimes(lhs, rhs) => z3.mkMul(exprToz3(lhs, varMap), exprToz3(rhs, varMap))
    case FDivision(lhs, rhs) => z3.mkDiv(exprToz3(lhs, varMap), exprToz3(rhs, varMap))
  }*/

}
