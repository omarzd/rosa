package leon
package numerics

import affine._
import purescala.Trees._
import purescala.TypeTrees._
import purescala.TreeOps._
import purescala.Definitions._
import purescala.Common._
import affine.{XFloat, XFloatConfig}


object Utils {
  val True = BooleanLiteral(true)
  val False = BooleanLiteral(false)

  def formatOption[T](res: Option[T]): String = res match {
    case Some(xf) => xf.toString
    case None => " -- "
  }

  val emptyRecord = Record(None, None, None, None, None)

  def getVariableRecords(expr: Expr): Map[Variable, Record] = {
    val collector = new VariableCollector
    collector.transform(expr)
    collector.recordMap
  }


  class VariableCollector extends TransformerWithPC {
    type C = Seq[Expr]
    val initC = Nil
    var recordMap: Map[Variable, Record] = Map.empty

    def register(e: Expr, path: C) = path :+ e

    override def rec(e: Expr, path: C) = e match {
      // a <= x
      case LessEquals(RationalLiteral(lwrBnd), x @ Variable(name)) =>
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord).updateLo(lwrBnd)); e
      // x <= b
      case LessEquals(x @ Variable(name), RationalLiteral(uprBnd)) =>
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord).updateUp(uprBnd)); e
      // a <= x
      case LessEquals(IntLiteral(lwrBnd), x @ Variable(name)) =>
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord).updateLo(Rational(lwrBnd))); e
      // x <= b
      case LessEquals(x @ Variable(name), IntLiteral(uprBnd)) =>
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord).updateUp(Rational(uprBnd))); e

      // a < x
      case LessThan(RationalLiteral(lwrBnd), x @ Variable(name)) =>
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord).updateLo(lwrBnd)); e
      // x < b
      case LessThan(x @ Variable(name), RationalLiteral(uprBnd)) =>
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord).updateUp(uprBnd)); e
      // a < x
      case LessThan(IntLiteral(lwrBnd), x @ Variable(name)) =>
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord).updateLo(Rational(lwrBnd))); e
      // x < b
      case LessThan(x @ Variable(name), IntLiteral(uprBnd)) =>
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord).updateUp(Rational(uprBnd))); e

      // b >= x
      case GreaterEquals(RationalLiteral(uprBnd), x @ Variable(name)) =>
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord).updateUp(uprBnd)); e
      // x >= a
      case GreaterEquals(x @ Variable(name), RationalLiteral(lwrBnd)) =>
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord).updateLo(lwrBnd)); e
      // b >= x
      case GreaterEquals(IntLiteral(uprBnd), x @ Variable(name)) =>
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord).updateUp(Rational(uprBnd))); e
      // x >= a
      case GreaterEquals(x @ Variable(name), IntLiteral(lwrBnd)) =>
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord).updateLo(Rational(lwrBnd))); e

      // b > x
      case GreaterThan(RationalLiteral(uprBnd), x @ Variable(name)) =>
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord).updateUp(uprBnd)); e
      // x > a
      case GreaterThan(x @ Variable(name), RationalLiteral(lwrBnd)) =>
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord).updateLo(lwrBnd)); e
      // b > x
      case GreaterThan(IntLiteral(uprBnd), x @ Variable(name)) =>
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord).updateUp(Rational(uprBnd))); e
      // x > a
      case GreaterThan(x @ Variable(name), IntLiteral(lwrBnd)) =>
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord).updateLo(Rational(lwrBnd))); e


      case Noise(x @ Variable(id), RationalLiteral(value)) =>
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord).updateAbsNoise(value)); e

      case Noise(x @ Variable(id), IntLiteral(value)) =>
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord).updateAbsNoise(Rational(value))); e

      case Noise(_, _) =>
        throw UnsupportedFragmentException(e.toString); e

      case RelError(x @ Variable(id), RationalLiteral(value)) =>
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord).updateRelNoise(value)); e

      case Roundoff(x @ Variable(id)) =>
        recordMap += (x -> recordMap.getOrElse(x, emptyRecord).addRndoff); e

      case _ =>
        super.rec(e, path)
    }

  }

  class ResultCollector extends TransformerWithPC {
    type C = Seq[Expr]
    val initC = Nil
    var lwrBound: Option[Rational] = None
    var upBound: Option[Rational] = None
    var error: Option[Rational] = None
    var errorExpr: Option[Expr] = None

    def initCollector = {
      lwrBound = None; upBound = None; error = None; errorExpr = None
    }

    def register(e: Expr, path: C) = path :+ e

    override def rec(e: Expr, path: C) = e match {
      case LessEquals(RationalLiteral(lwrBnd), ResultVariable()) => lwrBound = Some(lwrBnd); e
      case LessEquals(ResultVariable(), RationalLiteral(uprBnd)) => upBound = Some(uprBnd); e
      case LessEquals(IntLiteral(lwrBnd), ResultVariable()) => lwrBound = Some(Rational(lwrBnd)); e
      case LessEquals(ResultVariable(), IntLiteral(uprBnd)) => upBound = Some(Rational(uprBnd)); e
      case LessThan(RationalLiteral(lwrBnd), ResultVariable()) => lwrBound = Some(lwrBnd); e
      case LessThan(ResultVariable(), RationalLiteral(uprBnd)) =>  upBound = Some(uprBnd); e
      case LessThan(IntLiteral(lwrBnd), ResultVariable()) => lwrBound = Some(Rational(lwrBnd)); e
      case LessThan(ResultVariable(), IntLiteral(uprBnd)) => upBound = Some(Rational(uprBnd)); e
      case GreaterEquals(RationalLiteral(uprBnd), ResultVariable()) =>  upBound = Some(uprBnd); e
      case GreaterEquals(ResultVariable(), RationalLiteral(lwrBnd)) => lwrBound = Some(lwrBnd); e
      case GreaterEquals(IntLiteral(uprBnd), ResultVariable()) => upBound = Some(Rational(uprBnd)); e
      case GreaterEquals(ResultVariable(), IntLiteral(lwrBnd)) => lwrBound = Some(Rational(lwrBnd)); e
      case GreaterThan(RationalLiteral(uprBnd), ResultVariable()) =>  upBound = Some(uprBnd); e
      case GreaterThan(ResultVariable(), RationalLiteral(lwrBnd)) => lwrBound = Some(lwrBnd); e
      case GreaterThan(IntLiteral(uprBnd), ResultVariable()) => upBound = Some(Rational(uprBnd)); e
      case GreaterThan(ResultVariable(), IntLiteral(lwrBnd)) => lwrBound = Some(Rational(lwrBnd)); e

      case Noise(ResultVariable(), RationalLiteral(value)) => error = Some(value); e
      case Noise(ResultVariable(), IntLiteral(value)) => error = Some(Rational(value)); e

      case Noise(ResultVariable(), x) => errorExpr = Some(x); e
      case _ =>
        super.rec(e, path)
    }

    def getResultWithExpr(e: Expr): Option[(Rational, Rational, Expr)] = {
      initCollector
      rec(e, initC)
      println(lwrBound)
      println(upBound)
      println(error)
      println(errorExpr)
      if (!lwrBound.isEmpty && !upBound.isEmpty && (!error.isEmpty || !errorExpr.isEmpty)) {
        if (errorExpr.isEmpty) Some(lwrBound.get, upBound.get, RationalLiteral(error.get))
        else Some(lwrBound.get, upBound.get, errorExpr.get)
      } else
        None

    }

    def getResult(e: Expr): (Option[Rational], Option[Rational], Option[Rational]) = {
      initCollector
      rec(e, initC)
      (lwrBound, upBound, error)
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

        for (np <- nextPaths; cp <- currentPaths)
          newPaths = newPaths + cp.addPath(np)

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

  def mergeActualAPathResults(paths: Set[APath]): Map[Expr, (RationalInterval, Rational)] = {
    import Rational._

    var collection: Map[Expr, List[XFloat]] = Map.empty
    for (path <- paths) {
      for ((k, v) <- path.xfloats) {
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

  def noiseConstraintFromXFloats(results: Map[Expr, XFloat]): Expr = {
    And(results.foldLeft(Seq[Expr]())(
      (seq, kv) => seq :+ Noise(kv._1, RationalLiteral(kv._2.maxError))))
  }



  def constraintFromResults(results: Map[Expr, (RationalInterval, Rational)]): Expr = {
    And(results.foldLeft(Seq[Expr]())(
      (seq, kv) => seq ++ Seq(LessEquals(RationalLiteral(kv._2._1.xlo), kv._1),
                                  LessEquals(kv._1, RationalLiteral(kv._2._1.xhi)),
                                  Noise(kv._1, RationalLiteral(kv._2._2)))))
  }

  def constraintFromXFloats(results: Map[Expr, XFloat]): Expr = {
    And(results.foldLeft(Seq[Expr]())(
      (seq, kv) => seq ++ Seq(LessEquals(RationalLiteral(kv._2.realInterval.xlo), kv._1),
                                  LessEquals(kv._1, RationalLiteral(kv._2.realInterval.xhi)),
                                  Noise(kv._1, RationalLiteral(kv._2.maxError)))))
  }

  def actualConstraintFromResults(results: Map[Expr, (RationalInterval, Rational)]): Expr = {
    And(results.foldLeft(Seq[Expr]()) ((seq, kv) =>  interval2constraint(kv._1, kv._2._1, kv._2._2)))
  }

  private def interval2constraint(v: Expr, i: RationalInterval, e: Rational): Seq[Expr] = {
    val actualInterval = i + RationalInterval(-e, e)
    Seq(LessEquals(RationalLiteral(actualInterval.xlo), v),
                                  LessEquals(v, RationalLiteral(actualInterval.xhi)),
                                  Noise(v, RationalLiteral(e)))
  }

  def ratint2expr(r: RationalInterval, v: Expr): Expr = {
    And(LessEquals(RationalLiteral(r.xlo), v),
        LessEquals(v, RationalLiteral(r.xhi)))
  }




  class NoiseRemover extends TransformerWithPC {
    type C = Seq[Expr]
    val initC = Nil

    def register(e: Expr, path: C) = path :+ e

    override def rec(e: Expr, path: C) = e match {
      case Roundoff(_) => True
      case Noise(_, _) => True
      case RelError(_, _) => True
      case _ =>
        super.rec(e, path)
    }
  }


  class RoundoffRemover extends TransformerWithPC {
    type C = Seq[Expr]
    val initC = Nil

    def register(e: Expr, path: C) = path :+ e

    override def rec(e: Expr, path: C) = e match {
      case Roundoff(_) => True
      case _ =>
        super.rec(e, path)
    }
  }

  // Convenience for readability of printouts
  class DeltaRemover extends TransformerWithPC {
    type C = Seq[Expr]
    val initC = Nil

    def register(e: Expr, path: C) = path :+ e

    override def rec(e: Expr, path: C) = e match {
      case LessEquals(Variable(id1), Variable(id2)) if (id1.toString.contains("#delta_") && id2.toString == "#eps") =>
        True
      case LessEquals(UMinus(Variable(id1)), Variable(id2)) if (id1.toString == "#eps" && id2.toString.contains("#delta_")) =>
        True
      case _ =>
        super.rec(e, path)
    }
  }

  class BoundsConverter(eps2: Variable, offset: Variable) extends TransformerWithPC {
    type C = Seq[Expr]
    val initC = Nil

    def register(e: Expr, path: C) = path :+ e

    override def rec(e: Expr, path: C) = e match {
      case LessEquals(UMinus(eps), delta) if (eps.toString == "#eps") => LessThan(UMinus(eps2), delta)
      case LessEquals(delta, eps) if (eps.toString == "#eps") => LessThan(delta, eps2)
      case Equals(eps, machineEps) if (eps.toString == "#eps") => Equals(eps2, machineEps)

      case LessEquals(r @ RationalLiteral(v), x) => LessThan(Minus(r, offset), x)
      case GreaterEquals(x, r @ RationalLiteral(v)) => GreaterThan(x, Minus(r, offset))
      case LessEquals(x, y) => LessThan(x, Plus(y, offset))
      case GreaterEquals(x, y) => GreaterThan(Plus(x, offset), y)
      case _ =>
        super.rec(e, path)
    }
  }
}
