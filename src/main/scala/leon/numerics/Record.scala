package leon
package numerics

import ceres.common.Rational
import Utils.formatOption

case class Record(lo: Option[Rational], up: Option[Rational], noise: Option[Rational], rndoff: Option[Boolean]) {
  def updateLo(newLo: Rational): Record = Record(Some(newLo), up, noise, rndoff)
  def updateUp(newUp: Rational): Record = Record(lo, Some(newUp), noise, rndoff)
  def updateNoise(newNoise: Rational): Record = Record(lo, up, Some(newNoise), rndoff)
  def addRndoff: Record = Record(lo, up, noise, Some(true))

  def isComplete: Boolean = rndoff match {
    case Some(true) => (!lo.isEmpty && !up.isEmpty)
    case _ => (!lo.isEmpty && !up.isEmpty && !noise.isEmpty)
  }

  override def toString: String = "[%s, %s] (%s) (%s)".format(
     formatOption(lo), formatOption(up), formatOption(noise), formatOption(rndoff))
}

