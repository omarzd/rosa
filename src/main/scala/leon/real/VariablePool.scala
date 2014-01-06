/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import leon.purescala.Definitions._
import leon.purescala.Common._
import leon.purescala.TypeTrees._
import leon.purescala.Trees._
import purescala.TreeOps._

import real.Trees._
import Rational.{max, abs}

case class Record(ideal: Expr, actual: Expr, lo: Option[Rational], up: Option[Rational], absUncert: Option[Rational], relUncert: Option[Rational]) {
  def newLo(n: Rational): Record = Record(ideal, actual, Some(n), up, absUncert, relUncert)
  def newUp(n: Rational): Record = Record(ideal, actual, lo, Some(n), absUncert, relUncert)
  def newAbsUncert(n: Rational): Record = Record(ideal, actual, lo, up, Some(n), relUncert)
  def newRelUncert(n: Rational): Record = Record(ideal, actual, lo, up, absUncert, relUncert)

  def isBoundedValid: Boolean = !lo.isEmpty && !up.isEmpty && lo.get <= up.get

  def uncertainty: Option[Rational] =
    if (!absUncert.isEmpty) {
      absUncert
    } else {
      relUncert match {
      case Some(factor) =>
        val maxAbsoluteValue = factor * max(abs(lo.get), abs(up.get))
        Some(maxAbsoluteValue)
      case None => None
    }
  }

  override def toString: String = "%s = %s (%s, %s) +/- %s".format(ideal, actual,
    formatOption(lo), formatOption(up), formatOption(uncertainty))
}

object EmptyRecord extends Record(False, False, None, None, None, None)

/*
  Keeps track of ideal and the corresponding actual values, the associated uncertainties
  and such things.
  @param map indexed by ideal variable
*/
class VariablePool(inputs: Map[Expr, Record], val resId: Identifier) {
  import VariablePool._
  private var allVars = inputs

  allVars += (Variable(resId) -> emptyRecord(Variable(resId)))

  val resultVar = Variable(resId)
  val fResultVar = buddy(resultVar)

  def add(idSet: Set[Identifier]): Unit = {
    for (i <- idSet) {
      val v = Variable(i)
      if (! inputs.contains(v)) {
        allVars += (v -> emptyRecord(v))
      }
    }
  }

  def buddy(v: Expr): Expr = {
    if (allVars.contains(v)) {
      allVars(v).actual
    } else {
      val newRecord = emptyRecord(v)
      allVars += (v -> newRecord)
      newRecord.actual
    }
  }

  // not exhaustive, but if we don't find the variable, we have a bug
  def getIdeal(v: Expr): Expr = {
    allVars.find(x => x._2.actual == v) match {
      case Some((_, Record(i, a, _, _, _, _))) => i
      case _ => throw new Exception("not found: " + v)
    }
  }

  // When converting from actual to ideal in codegeneration, in conditionals we already have the ideal one
  def getIdealOrNone(v: Expr): Option[Expr] = {
    allVars.find(x => x._2.actual == v) match {
      case Some((_, Record(i, a, _, _, _, _))) => Some(i)
      case _ => None
    }
  }

  def getValidRecords: Iterable[Record] = allVars.values.filter(r => r.isBoundedValid)

  def actualVariables: Set[Expr] = allVars.values.map(rec => rec.actual).toSet

  def getInterval(v: Expr): RationalInterval = {
    val rec = allVars(v)
    RationalInterval(rec.lo.get, rec.up.get)
  }

  def hasValidInput(varDecl: Seq[VarDecl]): Boolean = {
    val params: Seq[Expr] = varDecl.map(vd => Variable(vd.id))
    if (inputs.size != params.size) {
      false
    } else {
      inputs.forall(v => params.contains(v._1) && v._2.isBoundedValid)
    }
  }

  def inputsWithoutNoise: Seq[Expr] = {
    inputs.filter(x => x._2.uncertainty.isEmpty).keySet.toSeq
  }

  override def toString: String = allVars.toString
}


object VariablePool {
  def emptyRecord(ideal: Expr): Record = ideal match {
    case Variable(id) => Record(ideal, Variable(FreshIdentifier("#" + id.name)).setType(RealType), None, None, None, None)
    case _ => new Exception("bug!"); EmptyRecord
  }

  def apply(expr: Expr, returnType: TypeTree): VariablePool = {
    val collector = new VariableCollector
    collector.transform(expr)
    new VariablePool(collector.recordMap, FreshIdentifier("result", true).setType(returnType))
  }

  private class VariableCollector extends TransformerWithPC {
    type C = Seq[Expr]
    val initC = Nil
    var recordMap = Map[Expr, Record]()

    def register(e: Expr, path: C): C = path :+ e

    // (Sound) Overapproximation in the case of strict inequalities
    override def rec(e: Expr, path: C): Expr = e match {
      case LessEquals(RealLiteral(lwrBnd), x @ Variable(_)) => // a <= x
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord(x)).newLo(lwrBnd)); e

      case LessEquals(x @ Variable(_), RealLiteral(uprBnd)) => // x <= b
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord(x)).newUp(uprBnd)); e

      case LessThan(RealLiteral(lwrBnd), x @ Variable(_)) => // a < x
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord(x)).newLo(lwrBnd)); e

      case LessThan(x @ Variable(_), RealLiteral(uprBnd)) => // x < b
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord(x)).newUp(uprBnd)); e

      case GreaterEquals(RealLiteral(uprBnd), x @ Variable(_)) => // b >= x
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord(x)).newUp(uprBnd)); e

      case GreaterEquals(x @ Variable(_), RealLiteral(lwrBnd)) => // x >= a
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord(x)).newLo(lwrBnd)); e

      case GreaterThan(RealLiteral(uprBnd), x @ Variable(_)) => // b > x
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord(x)).newUp(uprBnd)); e

      case GreaterThan(x @ Variable(_), RealLiteral(lwrBnd)) => // x > a
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord(x)).newLo(lwrBnd)); e

      case Noise(x @ Variable(_), RealLiteral(value)) =>
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord(x)).newAbsUncert(value)); e

      case Noise(_, _) =>
        throw UnsupportedRealFragmentException(e.toString); e

      case RelError(x @ Variable(id), RealLiteral(value)) =>
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord(x)).newRelUncert(value)); e

      case WithIn(x @ Variable(_), lwrBnd, upBnd) =>
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord(x)).newLo(lwrBnd).newUp(upBnd)); e

      case WithIn(e, lwrBnd, upBnd) =>
        throw UnsupportedRealFragmentException(e.toString); e

      case _ =>
        super.rec(e, path)

    }

  }

}
