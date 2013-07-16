package leon
package numerics

import affine.Rational
import Utils.formatOption

case class Record(lo: Option[Rational], up: Option[Rational], absNoise: Option[Rational], relNoise: Option[Rational],
  rndoff: Option[Boolean]) {
  assert(absNoise.isEmpty || relNoise.isEmpty)
  def updateLo(newLo: Rational): Record = Record(Some(newLo), up, absNoise, relNoise, rndoff)
  def updateUp(newUp: Rational): Record = Record(lo, Some(newUp), absNoise, relNoise, rndoff)
  def updateAbsNoise(newNoise: Rational): Record = Record(lo, up, Some(newNoise), relNoise, rndoff)
  def updateRelNoise(newNoise: Rational): Record = Record(lo, up, absNoise, Some(newNoise), rndoff)
  def addRndoff: Record = Record(lo, up, absNoise, relNoise, Some(true))

  def isComplete: Boolean = (!lo.isEmpty && !up.isEmpty)

  override def toString: String = "[%s, %s] (%s) (%s) (%s)".format(
     formatOption(lo), formatOption(up), formatOption(absNoise), formatOption(relNoise), formatOption(rndoff))
}

