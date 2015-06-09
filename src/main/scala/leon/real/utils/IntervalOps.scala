/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package real

import purescala.Trees._
import real.Trees._
import Rational._

trait IntervalOps {

  // for the same number of subdivisions on each variable
  def carthesianProduct(vars: Map[Expr, RationalInterval], n: Int): Seq[Map[Expr, RationalInterval]] = {

    val divisions: Map[Expr, Seq[RationalInterval]] = vars.map({
      case (e, int) => 
        val subSize = int.width / Rational(n)
        val a = int.xlo
        (e, for (i <- 0 until n) yield 
            RationalInterval(a + Rational(i) * subSize, a + Rational(i+1) * subSize))
      })

    val (x, ints) = divisions.head
    val startMap: Seq[Map[Expr, RationalInterval]] = ints.map(i => Map((x -> i)))

    divisions.tail.foldLeft(startMap)({
      case (cProd, (x, ints)) =>

        cProd.flatMap( t => for (xi <- ints) yield t + (x -> xi) )

      })

  }

  def carthesianProductXNum(vars: Map[Expr, XNum], n: Int, precision: Precision): Seq[Map[Expr, XNum]] = {

    val divisions: Map[Expr, Seq[XNum]] = vars.map({
      case (v @ Variable(_), xnum) =>
        val int = xnum.realRange.interval 
        val subSize = int.width / Rational(n)
        val a = int.xlo
        (v, for (i <- 0 until n) yield {
          val newInt = RationalInterval(a + Rational(i) * subSize, a + Rational(i+1) * subSize)
          XNum(v, newInt, TreeOps.rangeConstraint(v, newInt), Set(), xnum.maxError, false)(precision)
        })
      })

    val (x, ints) = divisions.head
    val startMap: Seq[Map[Expr, XNum]] = ints.map(i => Map((x -> i)))

    divisions.tail.foldLeft(startMap)({
      case (cProd, (x, ints)) =>

        cProd.flatMap( t => for (xi <- ints) yield t + (x -> xi) )

      })

  }

  // TODO: microbenchmark whether putting vars in an outer function
  // and not passing it around is faster
  def eval(e: Expr, vars: Map[Expr, RationalInterval]): RationalInterval = e match {
    case RealLiteral(r) => RationalInterval(r, r)
    case v @ Variable(_) => vars(v)
    case UMinusR(t) => - eval(t, vars)
    case PlusR(l, r) => eval(l, vars) + eval(r, vars)
    case MinusR(l, r) => eval(l, vars) - eval(r, vars)     
    case TimesR(l, r) => eval(l, vars) * eval(r, vars)
      
    case DivisionR(l, r) => eval(l, vars) / eval(r, vars)
      
    case SqrtR(t) =>
      val tt = eval(t, vars)
      RationalInterval(sqrtDown(tt.xlo), sqrtUp(tt.xhi))

    case PowerR(lhs, IntLiteral(p)) =>
      assert(p > 1, "p is " + p + " in " + e)
      val lhsInIntervals = eval(lhs, vars)
      var x = lhsInIntervals
      for (i <- 1 until p ){
        x = x * lhsInIntervals
      }
      x
  }

  def getRangeWithSubdivisions(e: Expr, vars: Map[Expr, RationalInterval], n: Int): RationalInterval = {

    val subdivisions = carthesianProduct(vars, n)

    val ranges = subdivisions.map(eval(e, _))

    ranges.tail.foldLeft(ranges.head)({
      case (total, range) => total.union(range)
      })
  }

  /*def getRangeSubdivisions(expr: Expr, vars: Map[Expr, RationalInterval]): RationalInterval = {
    // subdivide intervals
    val subdivisions = vars.map((e, i) => (e, ))

    // compute for each interval


    // merge intervals
  }*/

}