package leon
package numerics

import purescala.Trees._

import ceres.common.niceDoubleString

/**
  Class for storing partial bounds on variables.
 */
case class ParRange(lo: Option[Double], hi: Option[Double]) {
  def isDefined: Boolean = (lo, hi) match {
    case (Some(d1), Some(d2)) => true
    case _ => false
  }

  override def toString: String = (lo, hi) match {
    case (Some(d1), Some(d2)) =>
      "[%s,%s]".format(niceDoubleString(d1), niceDoubleString(d2))
    case (Some(d1), None) =>
      "[%s, ?]".format(niceDoubleString(d1))
    case (None, Some(d2)) =>
      "[?, %s]".format(niceDoubleString(d2))
    case (None, None) =>
      "[?, ?]"
    }



  def checkAndMerge(other: ParRange, reporter: Reporter,
    varName: Variable): ParRange = {
    val lwrBnd = this.lo match {
      case Some(v1) => other.lo match {
          case Some(v2) =>
            reporter.error("Found two lower bounds for " + varName)
            None
          case None => this.lo
        }
      case None => other.lo
    }
    val upBnd = this.hi match {
      case Some(v1) => other.hi match {
        case Some(v2) =>
          reporter.error("Found two upper bounds for " + varName)
          None
          case None => this.hi
      }
      case None => other.hi
    }
    ParRange(lwrBnd, upBnd)
  }
}


