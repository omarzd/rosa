package leon
package numerics

import ceres.common._

import purescala.Trees._

object Utils {

  // Omits those variables whose bounds are not fully defined or doubly defined.
  def getVariableBounds(expr: Expr): Map[Variable, RationalInterval] = {
    getPartialBounds(expr).collect {
      case (k, ParRange(Some(d1), Some(d2))) => (k, RationalInterval(d1, d2))
    }
  }

  /**
    Class for storing partial bounds on variables.
   */
  case class ParRange(lo: Option[Rational], hi: Option[Rational]) {
      
    override def toString: String = (lo, hi) match {
      case (Some(d1), Some(d2)) => "[%s,%s]".format(d1, d2)
      case (Some(d1), None) => "[%s, ?]".format(d1)
      case (None, Some(d2)) => "[?, %s]".format(d2)
      case (None, None) => "[?, ?]"
      }
  
  
  
    def checkAndMerge(other: ParRange, varName: Variable): ParRange = {
      val lwrBnd = this.lo match {
        case Some(v1) => other.lo match {
            case Some(v2) => None
            case None => this.lo
          }
        case None => other.lo
      }
      val upBnd = this.hi match {
        case Some(v1) => other.hi match {
          case Some(v2) => None
            case None => this.hi
        }
        case None => other.hi
      }
      ParRange(lwrBnd, upBnd)
    }
  }

  val emptyInterval = ParRange(None, None)

  // For now only accept bound given as follows:
  // ... && x <= 8.9 && 7.8 <= x && ...
  private def getPartialBounds(expr: Expr): Map[Variable, ParRange] = expr match {
    case LessEquals(RationalLiteral(lwrBnd), x @ Variable(name)) =>
      Map(x -> ParRange(Some(lwrBnd), None))
    case LessEquals(x @ Variable(name), RationalLiteral(uprBnd)) =>
      Map(x -> ParRange(None, Some(uprBnd)))
    case LessEquals(IntLiteral(lwrBnd), x @ Variable(name)) =>
      Map(x -> ParRange(Some(Rational(lwrBnd)), None))
    case LessEquals(x @ Variable(name), IntLiteral(uprBnd)) =>
      Map(x -> ParRange(None, Some(Rational(uprBnd))))

    case GreaterEquals(RationalLiteral(uprBnd), x @ Variable(name)) =>
      Map(x -> ParRange(None, Some(uprBnd)))
    case GreaterEquals(x @ Variable(name), RationalLiteral(lwrBnd)) =>
      Map(x -> ParRange(Some(lwrBnd), None))
    case GreaterEquals(IntLiteral(uprBnd), x @ Variable(name)) =>
      Map(x -> ParRange(None, Some(Rational(uprBnd))))
    case GreaterEquals(x @ Variable(name), IntLiteral(lwrBnd)) =>
      Map(x -> ParRange(Some(Rational(lwrBnd)), None))

    case And(exprs) =>
      var map: Map[Variable, ParRange] = Map.empty
      for (e <- exprs) {
        val map2 = getPartialBounds(e)
        map = map ++ map2.map{ case (k, v) =>
          k -> v.checkAndMerge(map.getOrElse(k, emptyInterval), k)}
      }
      map

    case _ => Map.empty
  }




}
