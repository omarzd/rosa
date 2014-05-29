/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import purescala.Trees._
import purescala.Common._

import real.Trees.{RealLiteral, Noise}


 /**
    Represents a specification of a variable.
    @param id real/ideal identifier this spec belongs to
    @param bounds real-valued (ideal) bounds
    @param absError maximum absolute error
  */
  //case class Spec(id: Identifier, bounds: RationalInterval, absError: Rational)

  case class Spec(id: Identifier, bounds: RationalInterval, absError: Option[Rational]) {
    def toRealExpr: Expr = {
      And(LessEquals(RealLiteral(bounds.xlo), Variable(id)),
            LessEquals(Variable(id), RealLiteral(bounds.xhi)))
    }

    def toExpr: Expr = absError match {
      case Some(absError) =>
        And(And(LessEquals(RealLiteral(bounds.xlo), Variable(id)),
            LessEquals(Variable(id), RealLiteral(bounds.xhi))),
            Noise(Variable(id), RealLiteral(absError)))
      case None =>
        println("---> SPEC without error")
        And(LessEquals(RealLiteral(bounds.xlo), Variable(id)),
          LessEquals(Variable(id), RealLiteral(bounds.xhi)))  
    }

    def getActualRange: RationalInterval = {
      RationalInterval(bounds.xlo - absError.get, bounds.xhi + absError.get)
    }

    override def toString: String = absError match {
      case Some(err) => id + " \u2208 " + bounds + " \u00B1 " + err
      case None => id + " \u2208 " + bounds + " \u00B1 -"
    }

    def addPathError(r: Rational): Spec = absError match {
      case Some(currentError) =>
        Spec(id, bounds, Some(Rational.max(currentError, r)))
      case None =>
        Spec(id, bounds, Some(r))
    }
  }