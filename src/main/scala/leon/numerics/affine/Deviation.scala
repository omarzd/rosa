package leon.numerics.affine

import ceres.common._
import Rational._


case class MismatchedException(msg: String) extends Exception(msg)


object Deviation {
  var currIndex: Int = 0
  def newIndex: Int = {
    currIndex += 1
    assert(currIndex != Int.MaxValue, "Affine indices just ran out...")
    currIndex
  }

  def apply(i: Int, v: Rational): Deviation = ConstantDev(i, v)

  val dummyDev = ConstantDev(Int.MaxValue, Rational.zero)
}

import Deviation._

/**
  An uncertainty with a unique index (except ZeroDeviation) and a value.
  The value may be positive and negative, thus indicating a direction.
  @param index noise index 
  @param value magnitude of this noise term
 */
abstract class Deviation(val index: Int, val value: Rational) {
  def unary_-(): Deviation
  def +(other: Deviation): Deviation
  def -(other: Deviation): Deviation
  def *(factor: Rational): Deviation
  def *(y: Deviation): Deviation
  def isZero: Boolean = (value == Rational.zero)
  override def toString: String = value.toDouble.toString + "e" + index
}


/**
  Deviation with value defined by a constant.
 */
case class ConstantDev(i: Int, v: Rational) extends Deviation(i, v) {
  def unary_-(): Deviation = ConstantDev(index, -v)
  
  def +(other: Deviation): Deviation = other match {
    case ConstantDev(i2, v2) if (i == i2) => Deviation(i, v + v2)
    case _ =>
      throw MismatchedException("Indices or types don't match."); null
  }

  def -(other: Deviation): Deviation = other match {
    case ConstantDev(i2, v2) if (i == i2) => Deviation(i, v - v2)
    case _ =>
      throw MismatchedException("Indices or types don't match."); null
  }

  def *(factor: Rational): Deviation = Deviation(i, v * factor)

  def *(y: Deviation): Deviation = y match {
    case ConstantDev(j, w) => Deviation(newIndex, v * w)
    case VariableDev(j, w, h) => VariableDev(newIndex, v * w, h)
  }
}

/**
  Keeps track of it's history, ie which initial indices it has been computed from.
  @param history list of indices of noise terms this one has been computed from
  For example, if you multiply x1e1 * x2e2 = (x1*x2)*e3 [1,2].
  Multiple indices are possible, [1,1] for example stands for e1*e1.
  We don't do this for all inputs and uncertainties, as we only interested in those
  from inputs.
 */
case class VariableDev(i: Int, v: Rational, history: List[Int]) extends Deviation(i, v) {
  def unary_-(): Deviation = VariableDev(index, -v, history)
  
  def +(other: Deviation): Deviation = other match {
    case VariableDev(i2, v2, h2) if (index == i2 && history == h2) =>
      VariableDev(index, v + v2, history)
    case _ =>
      throw MismatchedException("Indices or types don't match."); null
  }

  def -(other: Deviation): Deviation = other match {
    case VariableDev(i2, v2, h2) if (index == i2 && history == h2) =>
      VariableDev(index, v - v2, history)
    case _ =>
      throw MismatchedException("Indices or types don't match."); null
  }

  def *(factor: Rational): Deviation = VariableDev(index, v * factor, history)

  def *(y: Deviation): Deviation = y match {
    case ConstantDev(j, w) => VariableDev(newIndex, v * w, history)
    case VariableDev(j, w, h) => VariableDev(newIndex, v * w, history ++ h)
  }

  override def toString: String = value.toDouble.toString + "f" + index + "[" +history+"]"
}


