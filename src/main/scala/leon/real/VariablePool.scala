/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import purescala.TransformerWithPC
import leon.purescala.Definitions._
import leon.purescala.Common._
import leon.purescala.TypeTrees._
import leon.purescala.Trees._
import purescala.TreeOps._
import Precision._

import real.Trees._
import Rational.{max, abs}

case class Record(ideal: Expr, actual: Expr, lo: Option[Rational], up: Option[Rational],
  absUncert: Option[Rational], relUncert: Option[Rational]) {
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
class VariablePool(val inputs: Map[Expr, Record], val resIds: Seq[Identifier],
  val loopCounter: Option[Identifier], val integers: Seq[Identifier]) {

  import VariablePool._
  private var allVars = inputs

  val resultVars = resIds.map(Variable(_))
  resultVars foreach ( resVar =>
    allVars += (resVar -> emptyRecord(resVar))
  )

  val fResultVars = resultVars.map( buddy(_) )

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

  // TODO: move elsewhere
  def getVariableRecord(id: Identifier, specExpr: Expr): Record = {
    val (records, loopC, int) = collectVariables(specExpr)
    records(Variable(id))
  }


  def addVariableWithRange(id: Identifier, specExpr: Expr) = {
    val (records, loopC, int) = collectVariables(specExpr)
    val record = records(Variable(id))
    //println("record to add: " + record)
    allVars += (Variable(id) -> record) 
  }

  def getValidRecords: Iterable[Record] = allVars.values.filter(r => r.isBoundedValid)

  def getValidInputRecords: Iterable[Record] = {
    val inputIds = inputs.keys.toSeq
    allVars.filter(x => inputIds.contains(x._1) && x._2.isBoundedValid).values
  }

  def getValidTmpRecords: Iterable[Record] = {
    val inputIds = inputs.keys.toSeq
    allVars.filter(x => !inputIds.contains(x._1) && x._2.isBoundedValid).values
  }

  def actualVariables: Set[Expr] = allVars.values.map(rec => rec.actual).toSet

  def getInterval(v: Expr): RationalInterval = {
    val rec = allVars(v)
    RationalInterval(rec.lo.get, rec.up.get)
  }

  def getInitIntervals: Map[Expr, RationalInterval] = {
    inputs.map(x => (x._1 -> RationalInterval(x._2.lo.get - x._2.absUncert.get, x._2.up.get + x._2.absUncert.get)))
  }

  def hasValidInput(varDecl: Seq[ValDef], reporter: Reporter): Boolean = {
    //println("params: " + varDecl(0) + "   " + varDecl(1))
    val params: Seq[Expr] = varDecl.map(vd => Variable(vd.id))
    if (loopCounter.isEmpty) {
      (inputs.size == params.size && inputs.forall(v => params.contains(v._1) && v._2.isBoundedValid))  
    } else {
      (inputs.size == params.size - 1 && inputs.forall(v => params.contains(v._1) && v._2.isBoundedValid))
    }
    
  }

  def inputsWithoutNoise: Seq[Expr] = {
    inputs.filter(x => x._2.uncertainty.isEmpty).keySet.toSeq
  }

  def isLoopCounter(x: Expr): Boolean = (loopCounter, x) match {
    case (Some(l), Variable(id)) => l == id 
    case _ => false
  }

  def isInteger(x: Expr): Boolean = x match {
    case Variable(id) => integers.contains(id)
    case _ => false
  }

  def copyAndReplaceActuals(newActuals: Map[Expr, Expr]): VariablePool = {
    val newInputs = inputs.map({
      case (ideal, Record(i, a, lo, up, absUncert, relUncert)) =>
        (ideal, Record(i, newActuals(a), lo, up, absUncert, relUncert))
      })
    new VariablePool(newInputs, resIds, loopCounter, integers)
  }

  def getInitialErrors(precision: Precision): Map[Identifier, Rational] = precision match {
    case FPPrecision(_) => 
      throw new Exception("getInitialErrors doesn't work yet for fixed-points")
    case _ =>
      var map = Map[Identifier, Rational]()
      val machineEps = getUnitRoundoff(precision)
      inputs.map({
        case (Variable(id), Record(_,_, Some(lo),Some(up), Some(absError), _)) =>
          map += (id -> absError)
        case (Variable(id), Record(_,_, Some(lo),Some(up), _, _)) =>
          map += (id -> machineEps * max(abs(lo), abs(up)))
      })
      map
  }


  override def toString: String = allVars.toString 
}


object VariablePool {
  def emptyRecord(ideal: Expr): Record = ideal match {
    case Variable(id) => Record(ideal, Variable(FreshIdentifier("#" + id.name)).setType(RealType), None, None, None, None)
    case _ => new Exception("bug!"); EmptyRecord
  }

  def apply(expr: Expr, returnType: TypeTree): VariablePool = {
    val (records, loopC, int) = collectVariables(expr)
    
    val resIds = returnType match {
      case TupleType(baseTypes) =>
        baseTypes.zipWithIndex.map( {
          case (baseType, i) => FreshIdentifier("result" + i, true).setType(baseType)
          })

      case _ =>
        Seq(FreshIdentifier("result", true).setType(returnType))
    }

    new VariablePool(records, resIds, loopC, int)
  }

  def collectVariables(expr: Expr): (Map[Expr, Record], Option[Identifier], Seq[Identifier]) = {
    var recordMap = Map[Expr, Record]()
    var loopCounter: Option[Identifier] = None
    var integer: Seq[Identifier] = Seq.empty

    // (Sound) Overapproximation in the case of strict inequalities
    def addBound(e: Expr) = e match {  
      case LessEquals(RealLiteral(lwrBnd), x @ Variable(_)) => // a <= x
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord(x)).newLo(lwrBnd))

      case LessEquals(x @ Variable(_), RealLiteral(uprBnd)) => // x <= b
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord(x)).newUp(uprBnd))

      case LessThan(RealLiteral(lwrBnd), x @ Variable(_)) => // a < x
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord(x)).newLo(lwrBnd))

      case LessThan(x @ Variable(_), RealLiteral(uprBnd)) => // x < b
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord(x)).newUp(uprBnd))

      case GreaterEquals(RealLiteral(uprBnd), x @ Variable(_)) => // b >= x
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord(x)).newUp(uprBnd))

      case GreaterEquals(x @ Variable(_), RealLiteral(lwrBnd)) => // x >= a
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord(x)).newLo(lwrBnd))

      case GreaterThan(RealLiteral(uprBnd), x @ Variable(_)) => // b > x
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord(x)).newUp(uprBnd))

      case GreaterThan(x @ Variable(_), RealLiteral(lwrBnd)) => // x > a
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord(x)).newLo(lwrBnd))

      case Equals(x @ Variable(_), RealLiteral(value)) => // x == value
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord(x)).newLo(value))
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord(x)).newUp(value))

      case Equals(RealLiteral(value), x @ Variable(_)) => // x == value
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord(x)).newLo(value))
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord(x)).newUp(value))
        
      case Noise(x @ Variable(_), RealLiteral(value)) =>
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord(x)).newAbsUncert(value))

      case Noise(_, _) =>
        throw UnsupportedRealFragmentException(expr.toString)

      case RelError(x @ Variable(id), RealLiteral(value)) =>
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord(x)).newRelUncert(value))

      case WithIn(x @ Variable(_), lwrBnd, upBnd) =>
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord(x)).newLo(lwrBnd).newUp(upBnd))

      case WithIn(e, lwrBnd, upBnd) =>
        throw UnsupportedRealFragmentException(expr.toString)

      case LoopCounter(id) =>
        if (loopCounter.isEmpty) loopCounter = Some(id)
        else {
          throw UnsupportedRealFragmentException("two loop counters are not allowed")
        }

      case IntegerValue(id) => integer = integer :+ id

      case _ =>;
    }

    // Only extract bounds from simple clauses, not, e.g. from disjunctions
    expr match {
      case And(args) => args.foreach(a => addBound(a))
      case x => addBound(x)
    }

    (recordMap, loopCounter, integer)
  }

}
