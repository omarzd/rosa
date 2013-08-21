/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import purescala.Trees._
import purescala.TreeOps.negate

import real.Trees._

object Utils {

  def formatOption[T](o: Option[T]): String = o match {
    case Some(x) => x.toString
    case None => " -- "
  }

  /*def collectPaths(expr: Expr): Set[Path] = expr match {
    case IfExpr(cond, thenn, elze) =>
      val thenPaths = collectPaths(thenn).map(p => p.addCondition(cond))
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
  }*/

  
  /*

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

  

  def actualConstraintFromResults(results: Map[Expr, (RationalInterval, Rational)]): Expr = {
    And(results.foldLeft(Seq[Expr]()) ((seq, kv) =>  interval2constraint(kv._1, kv._2._1, kv._2._2)))
  }

  def actualConstraintFromXFloats(results: Map[Expr, XFloat]): Expr = {
    And(results.foldLeft(Seq[Expr]())(
      (seq, kv) => seq ++ Seq(LessEquals(RationalLiteral(kv._2.interval.xlo), kv._1),
                                  LessEquals(kv._1, RationalLiteral(kv._2.interval.xhi)),
                                  Noise(kv._1, RationalLiteral(kv._2.maxError)))))
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
  }*/
}