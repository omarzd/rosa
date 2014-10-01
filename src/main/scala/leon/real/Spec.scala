/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import purescala.Trees._
import purescala.Common._

import real.Trees.{RealLiteral, Noise}
import Rational._

object Spec {

  // to avoid confusion with nested sequences
  type SpecTuple = Seq[Spec]
  val emptySpecTuple: SpecTuple = Seq.empty

  def mergeSpecs(currentSpec: SpecTuple, newSpecs: SpecTuple): SpecTuple = (currentSpec, newSpecs) match {
    case (Seq(), specs) => specs

    case (current, Seq()) => current

    case _ =>
      currentSpec.zip(newSpecs).map({
        case (SimpleSpec(id1, b1, Some(e1)), SimpleSpec(id2, b2, Some(e2))) =>
          val lowerBnd = min(b1.xlo, b2.xlo)
          val upperBnd = max(b1.xhi, b2.xhi)
          val err = max(e1, e2)
          assert(id1 == id2)
          SimpleSpec(id1, RationalInterval(lowerBnd, upperBnd), Some(err))

        case (LoopSpec(id1, k1, s1, b1, Some(err1)), LoopSpec(id2, k2, s2, b2, Some(err2))) =>
          assert(id2 == id2)
          val lowerBnd = min(b1.xlo, b2.xlo)
          val upperBnd = max(b1.xhi, b2.xhi)
          val err = max(err1, err2)
          val k = k1.zip(k2).map({ case (a, b) => max(a, b)})
          LoopSpec(id1, k, max(s1, s2), RationalInterval(lowerBnd, upperBnd), Some(err))
        })
  }

}

/**
  Represents a specification of a variable.
  @param id real/ideal identifier this spec belongs to
  @param realBounds real-valued (ideal) bounds
  @param absError maximum absolute error
*/
//case class Spec(id: Identifier, bounds: RationalInterval, absError: Rational)

sealed abstract class Spec(val id: Identifier, val realBounds: RationalInterval, val absError: Option[Rational]) {

  def toRealExpr: Expr = {
    And(LessEquals(RealLiteral(realBounds.xlo), Variable(id)),
          LessEquals(Variable(id), RealLiteral(realBounds.xhi)))
  }

  def toExpr: Expr = absError match {
    case Some(absError) =>
      And(And(LessEquals(RealLiteral(realBounds.xlo), Variable(id)),
          LessEquals(Variable(id), RealLiteral(realBounds.xhi))),
          Noise(Variable(id), RealLiteral(absError)))
    case None =>
      println("---> SPEC without error")
      And(LessEquals(RealLiteral(realBounds.xlo), Variable(id)),
        LessEquals(Variable(id), RealLiteral(realBounds.xhi)))  
  }

  def getActualRange: RationalInterval
}

case class SimpleSpec(i: Identifier, b: RationalInterval, e: Option[Rational]) extends Spec(i, b, e) {
  
  def getActualRange: RationalInterval = {
    RationalInterval(realBounds.xlo - absError.get, realBounds.xhi + absError.get)
  }

  override def toString: String = absError match {
    case Some(err) => id + " \u2208 " + realBounds + " \u00B1 " + err
    case None => id + " \u2208 " + realBounds + " \u00B1 -"
  }

  def addPathError(r: Rational): Spec = absError match {
    case Some(currentError) =>
      SimpleSpec(id, realBounds, Some(Rational.max(currentError, r)))
    case None =>
      SimpleSpec(id, realBounds, Some(r))
  }
}

// It's an overapproximation to use the actual bounds as the real/ideal ones..
case class LoopSpec(i: Identifier, K: Seq[Rational], sigma: Rational,
  actualBounds: RationalInterval, loopError: Option[Rational]) extends Spec(i, actualBounds, loopError) {

  def getActualRange: RationalInterval = actualBounds
}