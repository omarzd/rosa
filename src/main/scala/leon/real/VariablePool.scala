/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package real

import purescala.TransformerWithPC
import leon.purescala.Definitions._
import leon.purescala.Common._
import leon.purescala.TypeTrees._
import leon.purescala.Trees._
import purescala.TreeOps._
import Precision._
import Rational._

import real.Trees._
import Rational.{max, abs}


/*
  Keeps track of ideal and the corresponding actual values, the associated uncertainties
  and such things.
  @param inputs indexed by ideal variable, all records are valid, i.e. bounded
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
      allVars(v).actualExpr
    } else {
      val newRecord = emptyRecord(v)
      allVars += (v -> newRecord)
      newRecord.actualExpr
    }
  }

  // not exhaustive, but if we don't find the variable, we have a bug
  def getIdeal(v: Expr): Expr = {
    allVars.find(x => x._2.actualExpr == v) match {
      case Some((_, Record(i, a, _, _, _, _))) => Variable(i)
      case _ => throw new Exception("not found: " + v)
    }
  }

  // When converting from actual to ideal in codegeneration, in conditionals we already have the ideal one
  def getIdealOrNone(v: Expr): Option[Expr] = {
    allVars.find(x => x._2.actualExpr == v) match {
      case Some((_, Record(i, a, _, _, _, _))) => Some(Variable(i))
      case _ => None
    }
  }

  def addVariableWithRange(id: Identifier, specExpr: Expr) = {
    val (records, loopC, int) = collectVariables(specExpr)
    val record = records(Variable(id))
    //println("record to add: " + record)
    allVars += (Variable(id) -> record) 
  }

  def getValidRecords: Iterable[Record] = allVars.values.filter(
    rec => rec.lo <= rec.up)

  def getValidInputRecords: Iterable[Record] = {
    val inputIds = inputs.keys.toSeq
    allVars.filter(x => inputIds.contains(x._1)).values
  }

  def getValidTmpRecords: Iterable[Record] = {
    val inputIds = inputs.keys.toSeq
    allVars.filter(x => !inputIds.contains(x._1)).values
  }

  def actualVariables: Set[Expr] = allVars.values.map(rec => rec.actualExpr).toSet

  def getIdealInterval(v: Expr): RationalInterval = {
    val rec = allVars(v)
    RationalInterval(rec.lo, rec.up)
  }

  // TODO: this is not safe, absUncert may remain empty!
  def getInitIntervals(precision: Precision): Map[Expr, RationalInterval] = {

    val errors = getInitialErrors(precision)

    inputs.map({
      case (v, Record(id, lo, up, _, _, _)) =>
        val err = errors(id)
        (v -> RationalInterval(lo - err, up + err))
      })

    /*inputs.map({
      case (v, rec) if (rec.initialError.nonEmpty) =>
        (v -> RationalInterval(rec.lo - rec.initialError.get, rec.up + rec.initialError.get))  


      case (v, Record(id, lo, up, Some(absError), _, _)) =>
        (v -> RationalInterval(lo - absError, up + absError))


      case (v, Record(id, lo, up, _, _, _)) =>
        val rndoff = roundoff(max(abs(lo), abs(up)), precision)
        (v -> RationalInterval(lo - rndoff, up + rndoff))

    })*/

     //(x._1 -> RationalInterval(x._2.lo - x._2.absUncert.get, x._2.up + x._2.absUncert.get)))
  }

  def inputsWithoutNoiseAndNoInt: Seq[Expr] = {
    inputs.filter(x => x._2.absUncert.isEmpty && !integers.contains(x._2.idealId)).keySet.toSeq
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
      case (ideal, Record(i, lo, up, absUncert, a, relUncert)) =>
        (ideal, Record(i, lo, up, absUncert,
                        newActuals(Variable(a)).asInstanceOf[Variable].id, relUncert))
      })
    new VariablePool(newInputs, resIds, loopCounter, integers)
  }

  def getInitialErrors(precision: Precision): Map[Identifier, Rational] = {
    //var map = Map[Identifier, Rational]()
    inputs.map({
      case (_, rec) if (rec.initialError.nonEmpty) =>
        (rec.idealId -> rec.initialError.get)
      case (_, Record(id, _, _, Some(absError), _, _)) =>
        (id -> absError)
      case (_, Record(id, lo, up, _, _, _)) =>
        (id -> roundoff(max(abs(lo), abs(up)), precision) )
    })
    //map
  }


  override def toString: String = allVars.mkString("\n") + "\nloopCounter: " + loopCounter +"\nints: " + integers
}

case class Record(idealId: Identifier, lo: Rational, up: Rational, absUncert: Option[Rational],
  actualId: Identifier, relUncert: Option[Rational]) {

  def this(i: Identifier, l: Rational, u: Rational, abs: Option[Rational],
    relUncert: Option[Rational] = None) = {
    this(i, l, u, abs, FreshIdentifier("#" + i.name), relUncert)
  }

  val actualExpr: Expr = Variable(actualId).setType(RealType)
  
  var loAct: Option[Rational] = None
  var upAct: Option[Rational] = None

  var isInteger: Boolean = false

  // initial errors specified in the case of loops
  var initialError: Option[Rational] = None

  override def toString: String = initialError match {
    case Some(in) => 
      s"($idealId, $actualId)[$lo, $up] +/- $absUncert (initial: $initialError) ~[$loAct, $upAct]"
    case None =>
      s"($idealId, $actualId)[$lo, $up] +/- $absUncert ~[$loAct, $upAct]"
  }
    
}

class PartialRecord {

  var ideal: Identifier = null
  //var actual: Expr = null
  var lo: Rational = null
  var up: Rational = null
  var loAct: Rational = null
  var upAct: Rational = null
  var abs: Rational = null
  var rel: Rational = null

  var initialError: Option[Rational] = None

  var isInteger: Boolean = false
}

object VariablePool {

  def emptyRecord(ideal: Expr): Record = ideal match {
    case Variable(id) => new Record(ideal.asInstanceOf[Variable].id, one, -one, None)

    case _ => new Exception("bug!"); null
  }

  def getVariableRecord(id: Identifier, specExpr: Expr): Record = {
    val (records, loopC, int) = collectVariables(specExpr)
    records(Variable(id))
  }

  // Only returns a VariablePool if the precondition is complete
  def apply(expr: Expr, valDefs: Seq[ValDef], returnType: TypeTree): Option[VariablePool] = {
    var (records, loopC, int) = collectVariables(expr)
   
    if (loopC.isEmpty) {
      valDefs.find(vdef => vdef.fixedType == LoopCounterType) match {
        case Some(loopCounter) => loopC = Some(loopCounter.toVariable.id)
        case _ => ;
      }
    }

    val params: Seq[Expr] = valDefs.map(vd => Variable(vd.id))
    if ((loopC.isEmpty && (records.forall(v => params.contains(v._1))) ) ||
        (records.forall(v => params.contains(v._1)))) { 

      val resIds = returnType match {
        case TupleType(baseTypes) =>
          baseTypes.zipWithIndex.map( {
            case (baseType, i) => FreshIdentifier("result" + i, true).setType(baseType)
            })

        case _ =>
          Seq(FreshIdentifier("result", true).setType(returnType))
      }

      Some(new VariablePool(records, resIds, loopC, int))
    } else {
      None
    }
  }

  
  def collectVariables(expr: Expr): (Map[Expr, Record], Option[Identifier], Seq[Identifier]) = {
    var recordMap = Map[Expr, PartialRecord]()
    var loopCounter: Option[Identifier] = None
    var integer: Set[Identifier] = Set.empty

    def getRecord(ideal: Variable): PartialRecord = {
      if (recordMap.contains(ideal)) {
        recordMap(ideal)
      } else {
        val rec = new PartialRecord()
        rec.ideal = ideal.id
        recordMap += (ideal -> rec)
        rec
      }

    }

    def addInitialErrors(e: Expr): Unit = e match {
      case And(args) => args.foreach(arg => addInitialErrors(arg))

      case Noise(x @ Variable(_), RealLiteral(value)) =>
        getRecord(x).initialError = Some(value)
    }


    // (Sound) Overapproximation in the case of strict inequalities
    def addBound(e: Expr) = e match { 

      // Ranges real

      case LessEquals(RealLiteral(lwrBnd), x @ Variable(_)) => // a <= x
        getRecord(x).lo = lwrBnd

      case LessEquals(x @ Variable(_), RealLiteral(uprBnd)) => // x <= b
        getRecord(x).up = uprBnd

      case LessThan(RealLiteral(lwrBnd), x @ Variable(_)) => // a < x
        getRecord(x).lo = lwrBnd

      case LessThan(x @ Variable(_), RealLiteral(uprBnd)) => // x < b
        getRecord(x).up = uprBnd

      case GreaterEquals(RealLiteral(uprBnd), x @ Variable(_)) => // b >= x
        getRecord(x).up = uprBnd

      case GreaterEquals(x @ Variable(_), RealLiteral(lwrBnd)) => // x >= a
        getRecord(x).lo = lwrBnd

      case GreaterThan(RealLiteral(uprBnd), x @ Variable(_)) => // b > x
        getRecord(x).up = uprBnd

      case GreaterThan(x @ Variable(_), RealLiteral(lwrBnd)) => // x > a
        getRecord(x).lo = lwrBnd

      case Equals(x @ Variable(_), RealLiteral(value)) => // x == value
        getRecord(x).lo = value
        getRecord(x).up = value

      case Equals(RealLiteral(value), x @ Variable(_)) => // x == value
        getRecord(x).lo = value
        getRecord(x).up = value

      // Ranges actual

      case LessEquals(RealLiteral(lwrBnd), Actual(x @ Variable(_))) => // a <= x
        getRecord(x).loAct = lwrBnd

      case LessEquals(Actual(x @ Variable(_)), RealLiteral(uprBnd)) => // x <= b
        getRecord(x).upAct = uprBnd

      case LessThan(RealLiteral(lwrBnd), Actual(x @ Variable(_))) => // a < x
        getRecord(x).loAct = lwrBnd

      case LessThan(Actual(x @ Variable(_)), RealLiteral(uprBnd)) => // x < b
        getRecord(x).upAct = uprBnd

      case GreaterEquals(RealLiteral(uprBnd), Actual(x @ Variable(_))) => // b >= x
        getRecord(x).upAct = uprBnd

      case GreaterEquals(Actual(x @ Variable(_)), RealLiteral(lwrBnd)) => // x >= a
        getRecord(x).loAct = lwrBnd

      case GreaterThan(RealLiteral(uprBnd), Actual(x @ Variable(_))) => // b > x
        getRecord(x).upAct = uprBnd

      case GreaterThan(Actual(x @ Variable(_)), RealLiteral(lwrBnd)) => // x > a
        getRecord(x).loAct = lwrBnd

      case Equals(Actual(x @ Variable(_)), RealLiteral(value)) => // x == value
        getRecord(x).loAct = value
        getRecord(x).upAct = value

      case Equals(RealLiteral(value), Actual(x @ Variable(_))) => // x == value
        getRecord(x).loAct = value
        getRecord(x).upAct = value

      // Ranges loop variables

      case LessEquals(IntLiteral(lwrBnd), x @ Variable(id)) => // a <= x
        getRecord(x).lo = Rational(lwrBnd)
        getRecord(x).isInteger = true
        integer = integer + id
        loopCounter = Some(id)


      case LessEquals(x @ Variable(id), IntLiteral(uprBnd)) => // x <= b
        getRecord(x).up = Rational(uprBnd)
        getRecord(x).isInteger = true
        integer = integer  + id
        loopCounter = Some(id)

      // Errors
        
      case Noise(x @ Variable(_), RealLiteral(value)) =>
        getRecord(x).abs = value

      case Noise(_, _) =>
        throw UnsupportedRealFragmentException(expr.toString)

      case RelError(x @ Variable(id), RealLiteral(value)) =>
        getRecord(x).rel = value

      case WithIn(x @ Variable(_), lwrBnd, upBnd) =>
        getRecord(x).lo = lwrBnd
        getRecord(x).up = upBnd

      case WithIn(e, lwrBnd, upBnd) =>
        throw UnsupportedRealFragmentException(expr.toString)


      // Loops

      case InitialErrors(tr) => addInitialErrors(tr)


      /*case LoopCounter(id) =>
        if (loopCounter.isEmpty) loopCounter = Some(id)
        else {
          throw UnsupportedRealFragmentException("two loop counters are not allowed")
        }

      case IntegerValue(id) => integer = integer + id
      */
      // TODO: add extraction for actual bounds

      case _ =>;
    }

    // Only extract bounds from simple clauses, not, e.g. from disjunctions
    expr match {
      case And(args) => args.foreach(a => addBound(a))
      case x => addBound(x)
    }

    val fullRecords: Map[Expr, Record] = recordMap.filter(rec =>
      rec._2.lo != null && rec._2.up != null && rec._2.lo <= rec._2.up).map({
        case (k, rec) =>
          val newRecord = 
            if (rec.abs != null)
              new Record(rec.ideal, rec.lo, rec.up, Some(rec.abs))

            else if (rec.rel != null) {
              val tmp = new Record(rec.ideal, rec.lo, rec.up, Some(rec.rel * max(abs(rec.lo), abs(rec.up))),
                                  Some(rec.rel))
              tmp
            } else {
              new Record(rec.ideal, rec.lo, rec.up, None)
            }
          if (rec.loAct != null) newRecord.loAct = Some(rec.loAct)
          if (rec.upAct != null) newRecord.upAct = Some(rec.upAct)
          newRecord.isInteger = rec.isInteger
          newRecord.initialError = rec.initialError

          (k -> newRecord)
      })

    // TODO: check that we only have one loop counter 


    (fullRecords, loopCounter, integer.toSeq)
  }

}
