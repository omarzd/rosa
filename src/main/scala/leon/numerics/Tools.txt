package leon
package numerics

import ceres.common._
import ceres.smartfloat._

import purescala.Trees._
import purescala.Common._
import purescala.TreeOps._


class Tools(reporter: Reporter) {

  val simSize = 100000000

  def compare(vc: VerificationCondition): VerificationCondition = {
    reporter.info("Now simulating VC of function " + vc.funDef.id.name)
    val varInts = variables2intervals(vc.inputs)
    val varSmarts = variables2smartfloats(vc.inputs)

    //val t1 = System.nanoTime
    val intResult: Interval = inIntervals(vc.expr, varInts)
    //val t2 = System.nanoTime
    val smartResult: SmartFloat = inSmartFloats(vc.expr, varSmarts)
    //val t3 = System.nanoTime
    val simulationResult: Interval = simulate(vc.expr, varInts)
    //val t4 = System.nanoTime

    val resultString = "simulated: %s,\n|    intervals: %s,\n|    smartfloat: %s".format(
      simulationResult, intResult.toString, smartResult.toString  
    )
    vc.res = Some(resultString)
    vc
  }

  private def variables2intervals(vars: Map[Variable, ParRange]): Map[Variable, Interval] = {
    vars.collect {
      case (k, v) if (v.isDefined) => k -> Interval(v.lo.get, v.hi.get)
    }
  }

  private def variables2smartfloats(vars: Map[Variable, ParRange]): Map[Variable, SmartFloat] = {
    vars.collect {
      case (k, v) if (v.isDefined) =>
        val xlo = v.lo.get
        val xhi = v.hi.get
        val rad = (xhi - xlo) / 2
        val mid = xlo + rad
        k -> SmartFloat(mid.toDouble, rad.toDouble)
    }
  }

  private def inIntervals(tree: Expr, vars: Map[Variable, Interval]): Interval = tree match {
    case v @ Variable(id) => vars(v)
    case RationalLiteral(v) => Interval(v.toDouble) 
    case IntLiteral(v) => Interval(v)
    case FloatLiteral(v) => Interval(v)
    case UMinus(rhs) => - inIntervals(rhs, vars)
    case Plus(lhs, rhs) => inIntervals(lhs, vars) + inIntervals(rhs, vars)
    case Minus(lhs, rhs) => inIntervals(lhs, vars) - inIntervals(rhs, vars)
    case Times(lhs, rhs) => inIntervals(lhs, vars) * inIntervals(rhs, vars)
    case Division(lhs, rhs) => inIntervals(lhs, vars) / inIntervals(rhs, vars)
    // TODO: IntegerAsFloat
    case _ =>
      throw UnsupportedFragmentException("Can't handle: " + tree.getClass)
      null
  }

  private def inSmartFloats(tree: Expr, vars: Map[Variable, SmartFloat]): SmartFloat = tree match {
    case v @ Variable(id) => vars(v)
    case RationalLiteral(v) => SmartFloat(v.toDouble)
    case IntLiteral(v) => SmartFloat(v)
    case FloatLiteral(v) => SmartFloat(v)
    case UMinus(rhs) => - inSmartFloats(rhs, vars)
    case Plus(lhs, rhs) => inSmartFloats(lhs, vars) + inSmartFloats(rhs, vars)
    case Minus(lhs, rhs) => inSmartFloats(lhs, vars) - inSmartFloats(rhs, vars)
    case Times(lhs, rhs) => inSmartFloats(lhs, vars) * inSmartFloats(rhs, vars)
    case Division(lhs, rhs) => inSmartFloats(lhs, vars) / inSmartFloats(rhs, vars)
    // TODO: IntegerAsFloat
    case _ =>
      throw UnsupportedFragmentException("Can't handle: " + tree.getClass)
      null
  }

  private def simulate(tree: Expr, vars: Map[Variable, Interval]): Interval = {
    val r = new scala.util.Random(4753)

    var counter = 0
    var resInterval: Interval = EmptyInterval
    while(counter < simSize) {
      var randomInputs = new collection.immutable.HashMap[Variable, Double]()
      for ((k, v) <- vars) randomInputs += ((k, v.xlo + r.nextDouble * (v.xhi - v.xlo)))

      //println("\ninputs: " + randomInputs)
      val res = eval(tree, randomInputs)
      //println("res: " + res)
      //println("nputs: " + randomInputs)
      //println(eval(tree, randomInputs))
      

      resInterval = extendInterval(resInterval, res)
      counter += 1
    }
    resInterval 
  }

  private def extendInterval(i: Interval, d: Double): Interval = i match {
    case EmptyInterval => Interval(d)
    case NormalInterval(xlo, xhi) =>
      if (d >= xlo && d <= xhi) i
      else if (d <= xlo) NormalInterval(d, xhi)
      else if (d >= xhi) NormalInterval(xlo, d)
      else null
  }


  private def eval(tree: Expr, vars: Map[Variable, Double]): Double = tree match {
    case v @ Variable(id) => vars(v)
    case RationalLiteral(v) => v.toDouble
    case IntLiteral(v) => v.toDouble
    case FloatLiteral(v) => v
    case UMinus(rhs) => - eval(rhs, vars)
    case Plus(lhs, rhs) => eval(lhs, vars) + eval(rhs, vars)
    case Minus(lhs, rhs) => eval(lhs, vars) - eval(rhs, vars)
    case Times(lhs, rhs) => eval(lhs, vars) * eval(rhs, vars)
    case Division(lhs, rhs) => eval(lhs, vars) / eval(rhs, vars)
    // TODO: IntegerAsFloat
    case _ =>
      throw UnsupportedFragmentException("Can't handle: " + tree.getClass)
      Double.NaN
  }

}
