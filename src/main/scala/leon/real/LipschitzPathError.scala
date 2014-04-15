/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import purescala.Trees._

import real.TreeOps.{idealToActual}
import real.Trees.{PlusR, WithInEq}
import Rational.abs


class LipschitzPathError(reporter: Reporter, solver: RangeSolver, precision: Precision, variables: VariablePool) {

  val approximator = new AAApproximator(reporter, solver, precision, checkPathError = true)
  val leonToZ3 = new LeonToZ3Transformer(variables, precision)

  /*
    @param rPath path taken by real values
    @param fPath alternative path, possibly taken by floats
  */
  def computePathError(precondition: Expr, rPath: Path, fPath: Path): Seq[Rational] = {
    println("*****\nreal path: " + rPath.bodyReal)
    println("fl path:   " + fPath.bodyReal)
    println("pre: " + precondition)

    //compute I
    val cInt = computeCriticalInterval(precondition, rPath.condition) 

    //intersect with fPath condition

    // Lipschitz of f1, f2 on I


    // roundoff error of f1, f2 on I


    // difference between f1 and f2 over I


    Seq()
  }

  def computePathErrors(precondition: Expr, branchCond: Expr, thenn: Expr, elze: Expr,
    vars: Map[Expr, XReal]): Seq[Rational] = {

    //compute I
    //val cInt = computeCriticalInterval(precondition, branchCond, vars) 

    // Lipschitz of f1, f2 on I


    // roundoff error of f1, f2 on I


    // difference between f1 and f2 over I


    Seq()
  }

  /*
    Computes the expression characterizing the values where can have diverging control flow,
    and also the intervals, if such computation is possible.
    Is going to throw an Exception if the condition is not in a fragment that we can handle,
    for instance, if it contains a disjunction.
  */
  def computeCriticalInterval(precondition: Expr, cond: Expr): (Expr, Map[Expr, RationalInterval]) = {
    def isSimpleComparison(e: Expr): Boolean = e match {
      case GreaterThan(_,_) | GreaterEquals(_,_) | LessThan(_,_) | LessEquals(_,_) => true
      case _ => false
    }

    def toEquality(e: Expr): Expr = e match {
      case GreaterThan(l, r) =>   Equals(l, r)
      case GreaterEquals(l, r) =>   Equals(l, r)
      case LessThan(l, r) =>      Equals(l, r)
      case LessEquals(l, r) =>    Equals(l, r)
    }

    def addErrors(e: Expr): Expr = e match {
      case Equals(lhs, rhs) =>
        val lhsUncert = approximator.computeError(idealToActual(lhs, variables), precondition, variables, false)
        val rhsUncert = approximator.computeError(idealToActual(rhs, variables), precondition, variables, false)
        val totalUncert = abs(rhsUncert - lhsUncert)

        val freshVar = VariableShop.getNewDelta
        And(Equals(lhs, PlusR(rhs, freshVar)), WithInEq(freshVar, -totalUncert, totalUncert))
    }

    val clauses = cond match {
      case And(args) => args
      case x => Seq(x)
    }

    if (clauses.forall(c => isSimpleComparison(c))) {
      val exactBranchpoints = clauses.map(c => toEquality(c))

      val withErrors = exactBranchpoints.map(c => addErrors(c))

      //computeInterval
      variables.inputs.foreach({
        case (v @ Variable(_), Record(i, a, Some(lo), Some(hi), Some(err), None)) =>
          println("tightening: " + v)
          // I think we don't want the precondition here,
          // or maybe anything, but the range constraints
          val constraints = And(withErrors) //And(precondition, And(withErrors))
          println(constraints)
          println(RationalInterval(lo - err, hi + err))

          val interval = solver.tightenRange(v, leonToZ3.getZ3Condition(constraints),
            RationalInterval(lo - err, hi + err), solverMaxIterHigh, solverPrecisionHigh)
          println(" -> " + interval)
      })

      (And(withErrors), Map.empty)
    } else {
      throw new Exception("Cannot handle this branch condition for path error computation: " + cond)
      null
    }
  }

  

}