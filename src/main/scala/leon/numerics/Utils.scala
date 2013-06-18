package leon
package numerics

import ceres.common._

import purescala.Trees._
import purescala.TypeTrees._
import purescala.TreeOps._
import purescala.Definitions._
import purescala.Common._

import affine.XFloat


object Utils {
  private var errCounter = 0
  private var deltaCounter = 0
  private var sqrtCounter = 0
  private var fncCounter = 0
  private var resErrorCounter = 0

  def getNewErrorVar: Variable = {
    errCounter = errCounter + 1
    Variable(FreshIdentifier("#err_" + errCounter)).setType(RealType)
  }
  def getNewDelta: Variable = {
    deltaCounter = deltaCounter + 1
    Variable(FreshIdentifier("#delta_" + deltaCounter)).setType(RealType)
  }
  def getNewSqrtVariable: (Variable, Variable) = {
    sqrtCounter = sqrtCounter + 1
    (Variable(FreshIdentifier("#sqrt" + sqrtCounter)).setType(RealType),
      Variable(FreshIdentifier("#sqrt" + sqrtCounter + "_0")).setType(RealType))
  }

  def getNewFncVariable(id: String): Variable = {
    fncCounter = fncCounter + 1
    Variable(FreshIdentifier("#" + id + "_call_" + fncCounter)).setType(RealType)
  }

  def getNewResErrorVariable: Variable = {
    resErrorCounter = resErrorCounter + 1
    Variable(FreshIdentifier("#resErr" + resErrorCounter)).setType(RealType)
  }

  def getNamedError(v: Expr): Variable = {
    Variable(FreshIdentifier("#err_(" + v.toString + ")")).setType(RealType)
  }

  def getRndoff(expr: Expr): (Expr, Variable) = {
    val delta = getNewDelta
    (Times(expr, delta), delta)
  }

  def getFreshRndoffMultiplier: (Expr, Variable) = {
    val delta = getNewDelta
    (Plus(new RationalLiteral(1), delta) , delta)
  }




  def formatOption[T](res: Option[T]): String = res match {
    case Some(xf) => xf.toString
    case None => " -- "
  }

  val emptyRecord = Record(None, None, None, None)

  class VariableCollector extends TransformerWithPC {
    type C = Seq[Expr]
    val initC = Nil
    var recordMap: Map[Variable, Record] = Map.empty

    def register(e: Expr, path: C) = path :+ e

    override def rec(e: Expr, path: C) = e match {
      // a <= x
      case LessEquals(RationalLiteral(lwrBnd), x @ Variable(name)) =>
        recordMap = recordMap + (x -> recordMap.getOrElse(x, emptyRecord).updateLo(lwrBnd)); e
      // x <= b
      case LessEquals(x @ Variable(name), RationalLiteral(uprBnd)) =>
        recordMap = recordMap + (x -> recordMap.getOrElse(x, emptyRecord).updateUp(uprBnd)); e
      // a <= x
      case LessEquals(IntLiteral(lwrBnd), x @ Variable(name)) =>
        recordMap = recordMap + (x -> recordMap.getOrElse(x, emptyRecord).updateLo(Rational(lwrBnd))); e
      // x <= b
      case LessEquals(x @ Variable(name), IntLiteral(uprBnd)) =>
        recordMap = recordMap + (x -> recordMap.getOrElse(x, emptyRecord).updateUp(Rational(uprBnd))); e

      // b >= x
      case GreaterEquals(RationalLiteral(uprBnd), x @ Variable(name)) =>
        recordMap = recordMap + (x -> recordMap.getOrElse(x, emptyRecord).updateUp(uprBnd)); e
      // x >= a
      case GreaterEquals(x @ Variable(name), RationalLiteral(lwrBnd)) =>
        recordMap = recordMap + (x -> recordMap.getOrElse(x, emptyRecord).updateLo(lwrBnd)); e
      // b >= x
      case GreaterEquals(IntLiteral(uprBnd), x @ Variable(name)) =>
        recordMap = recordMap + (x -> recordMap.getOrElse(x, emptyRecord).updateUp(Rational(uprBnd))); e
      // x >= a
      case GreaterEquals(x @ Variable(name), IntLiteral(lwrBnd)) =>
        recordMap = recordMap + (x -> recordMap.getOrElse(x, emptyRecord).updateLo(Rational(lwrBnd))); e

      case Noise(x @ Variable(id), RationalLiteral(value)) =>
        recordMap = recordMap + (x -> recordMap.getOrElse(x, emptyRecord).updateNoise(value)); e

      case Noise(x @ Variable(id), IntLiteral(value)) =>
        recordMap = recordMap + (x -> recordMap.getOrElse(x, emptyRecord).updateNoise(Rational(value))); e

      case Roundoff(x @ Variable(id)) =>
        recordMap = recordMap + (x -> recordMap.getOrElse(x, emptyRecord).addRndoff); e

      case _ =>
        super.rec(e, path)
    }

  }

  def collectPaths(expr: Expr): Set[Path] = expr match {
    case IfExpr(cond, then, elze) =>
      val thenPaths = collectPaths(then).map(p => p.addCondition(cond))
      val elzePaths = collectPaths(elze).map(p => p.addCondition(negate(cond)))

      thenPaths ++ elzePaths

    case And(args) =>
      var currentPaths: Set[Path] = collectPaths(args.head)

      for (a <- args.tail) {
        var newPaths: Set[Path] = Set.empty

        val nextPaths = collectPaths(a)

        // TODO: in one loop?
        for (np <- nextPaths) {
          for (cp <- currentPaths) {
            newPaths = newPaths + cp.addPath(np)
          }
        }
        currentPaths = newPaths
      }
      currentPaths

    case Equals(e, f) =>
      collectPaths(f).map(p => p.addEqualsToLast(e))

    case _ =>
      Set(Path(BooleanLiteral(true), List(expr)))
  }


  /*
    Consolidates results from different paths by merging the intervals and finding the largest error.
   */
  def mergeRealPathResults(paths: Set[Path]): Map[Expr, (RationalInterval, Rational)] = {
    import Rational._

    var collection: Map[Expr, List[XFloat]] = Map.empty
    for (path <- paths) {
      for ((k, v) <- path.values) {
        collection = collection + ((k, List(v) ++ collection.getOrElse(k, List())))
      }
    }

    // Two options:
    // interval -> ranges of ACTUAL variables  (but in this case, the key is the buddy variable!)
    // realInterval -> ranges of IDEAL variables
    var resMap: Map[Expr, (RationalInterval, Rational)] = Map.empty
    for ((k, list) <- collection) {
      var lo = list.head.realInterval.xlo
      var hi = list.head.realInterval.xhi
      var err = list.head.maxError

      for (xf <- list.tail) {
        lo = min(lo, xf.realInterval.xlo)
        hi = max(hi, xf.realInterval.xhi)
        err = max(err, xf.maxError)
      }
      resMap = resMap + ((k, (RationalInterval(lo, hi), err)))
    }
    resMap
  }

  def mergeActualPathResults(paths: Set[Path]): Map[Expr, (RationalInterval, Rational)] = {
    import Rational._

    var collection: Map[Expr, List[XFloat]] = Map.empty
    for (path <- paths) {
      for ((k, v) <- path.values) {
        collection = collection + ((k, List(v) ++ collection.getOrElse(k, List())))
      }
    }

    // Two options:
    // interval -> ranges of ACTUAL variables  (but in this case, the key is the buddy variable!)
    // realInterval -> ranges of IDEAL variables
    var resMap: Map[Expr, (RationalInterval, Rational)] = Map.empty
    for ((k, list) <- collection) {
      var lo = list.head.interval.xlo
      var hi = list.head.interval.xhi
      var err = list.head.maxError

      for (xf <- list.tail) {
        lo = min(lo, xf.interval.xlo)
        hi = max(hi, xf.interval.xhi)
        err = max(err, xf.maxError)
      }
      resMap = resMap + ((k, (RationalInterval(lo, hi), err)))
    }
    resMap
  }

  def constraintFromResults(results: Map[Expr, (RationalInterval, Rational)]): Expr = {
    And(results.foldLeft(Seq[Expr]())(
      (seq, kv) => seq ++ Seq(LessEquals(RationalLiteral(kv._2._1.xlo), kv._1),
                                  LessEquals(kv._1, RationalLiteral(kv._2._1.xhi)),
                                  Noise(kv._1, RationalLiteral(kv._2._2)))))
  }

  def ratint2expr(r: RationalInterval, v: Expr): Expr = {
    And(LessEquals(RationalLiteral(r.xlo), v),
        LessEquals(v, RationalLiteral(r.xhi)))
  }

  /*
    Replaces all constructs related to Real's with something meant to compile.
  */
  class NoiseRemover extends TransformerWithPC {
    type C = Seq[Expr]
    val initC = Nil

    // TODO: do we need this?
    def register(e: Expr, path: C) = path :+ e

    override def rec(e: Expr, path: C) = e match {
      //case Noise(_, _) => BooleanLiteral(true)
      case Roundoff(expr) => BooleanLiteral(true)
      case _ =>
        super.rec(e, path)
    }

  }
}
