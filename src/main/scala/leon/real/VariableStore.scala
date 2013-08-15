/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import leon.purescala.Common._
import leon.purescala.TypeTrees._
import leon.purescala.Trees._
import purescala.TreeOps._

import real.Trees._

case class Record(ideal: Variable, actual: Variable, lo: Option[Rational], up: Option[Rational], uncertainty: Option[Rational]) {
  def newLo(n: Rational): Record = Record(ideal, actual, Some(n), up, uncertainty)
  def newUp(n: Rational): Record = Record(ideal, actual, lo, Some(n), uncertainty)
  def newUncert(n: Rational): Record = Record(ideal, actual, lo, up, Some(n))
}

/*
  Keeps track of ideal and the corresponding actual values, the associated uncertainties
  and such things.
@param map indexed by ideal variable
*/
class VariableStore(map: Map[Variable, Record]) {

  override def toString: String = map.toString
}


object VariableStore {

  def apply(expr: Expr): VariableStore = {
    val collector = new VariableCollector
    collector.transform(expr)
    new VariableStore(collector.recordMap)
  }

  private class VariableCollector extends TransformerWithPC {
    type C = Seq[Expr]
    val initC = Nil
    var recordMap = Map[Variable, Record]()

    def emptyRecord(ideal: Variable) =
      Record(ideal, Variable(FreshIdentifier("#" + ideal.id.name + "-r")).setType(RealType), None, None, None)


    def register(e: Expr, path: C) = path :+ e

    // (Sound) Overapproximation in the case of strict inequalities
    override def rec(e: Expr, path: C) = e match {
      case LessEquals(RationalLiteral(lwrBnd), x @ Variable(_)) => // a <= x
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord(x)).newLo(lwrBnd)); e
      
      case LessEquals(x @ Variable(_), RationalLiteral(uprBnd)) => // x <= b
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord(x)).newUp(uprBnd)); e

      case LessThan(RationalLiteral(lwrBnd), x @ Variable(_)) => // a < x
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord(x)).newLo(lwrBnd)); e
      
      case LessThan(x @ Variable(_), RationalLiteral(uprBnd)) => // x < b
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord(x)).newUp(uprBnd)); e
      
      case GreaterEquals(RationalLiteral(uprBnd), x @ Variable(_)) => // b >= x
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord(x)).newUp(uprBnd)); e
      
      case GreaterEquals(x @ Variable(_), RationalLiteral(lwrBnd)) => // x >= a
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord(x)).newLo(lwrBnd)); e
      
      case GreaterThan(RationalLiteral(uprBnd), x @ Variable(_)) => // b > x
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord(x)).newUp(uprBnd)); e
      
      case GreaterThan(x @ Variable(_), RationalLiteral(lwrBnd)) => // x > a
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord(x)).newLo(lwrBnd)); e
      
      case Noise(x @ Variable(_), RationalLiteral(value)) =>
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord(x)).newUncert(value)); e

      case Noise(_, _) =>
        throw UnsupportedRealFragmentException(e.toString); e

      case _ =>
        super.rec(e, path)
      
    }

  }

}




// a <= x
      /*case LessEquals(IntLiteral(lwrBnd), x @ Variable(name)) =>
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord).updateLo(Rational(lwrBnd))); e
      // x <= b
      case LessEquals(x @ Variable(name), IntLiteral(uprBnd)) =>
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord).updateUp(Rational(uprBnd))); e

      // a < x
      case LessThan(IntLiteral(lwrBnd), x @ Variable(name)) =>
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord).updateLo(Rational(lwrBnd))); e
      // x < b
      case LessThan(x @ Variable(name), IntLiteral(uprBnd)) =>
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord).updateUp(Rational(uprBnd))); e
      
      // b >= x
      case GreaterEquals(IntLiteral(uprBnd), x @ Variable(name)) =>
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord).updateUp(Rational(uprBnd))); e
      // x >= a
      case GreaterEquals(x @ Variable(name), IntLiteral(lwrBnd)) =>
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord).updateLo(Rational(lwrBnd))); e
      
      // b > x
      case GreaterThan(IntLiteral(uprBnd), x @ Variable(name)) =>
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord).updateUp(Rational(uprBnd))); e
      // x > a
      case GreaterThan(x @ Variable(name), IntLiteral(lwrBnd)) =>
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord).updateLo(Rational(lwrBnd))); e

      case Noise(x @ Variable(id), IntLiteral(value)) =>
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord).newUncert(Rational(value))); e

      case RelError(x @ Variable(id), RationalLiteral(value)) =>
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord).updateRelNoise(value)); e

      case Roundoff(x @ Variable(id)) =>
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord).addRndoff); e
      */