package leon.numerics.affine

import ceres.common._

import collection.mutable.Queue

case class DivisionByZeroException(s: String) extends Exception

object Deviation {
  var currIndex: Int = 0
  def newIndex: Int = {
    currIndex += 1
    assert(currIndex != Int.MaxValue, "Affine indices just ran out...")
    currIndex
  }

  case class MismatchedIndicesException(msg: String) extends Exception(msg)

  def apply(i: Int, v: Rational): Deviation = {
    if (v == Rational.zero) ZeroDev
    else ConstantDev(i, v)
  }
}

import Deviation._

/**
  An uncertainty with a unique index (except ZeroDeviation) and a value.
  The value may be positive and negative, thus indicating a direction.
 */
abstract class Deviation(val index: Int) {
  
  // max absolute value of this uncertainty
  def value: Rational

  def unary_-(): Deviation
  def +(other: Deviation): Deviation
  def -(other: Deviation): Deviation
  def *(factor: Rational): Deviation

  override def toString: String = value.toDouble.toString + "e" + index
  //def toErrorString: String = value.toDouble.toString + "r" + index
}

/**
  Special case of a deviation for zero values.
  This is the only one that has a non-unique index.
 */
case object ZeroDev extends Deviation(Int.MaxValue) {
  def value = Rational.zero
  def unary_-(): Deviation = ZeroDev
  def +(other: Deviation): Deviation = other
  def -(other: Deviation): Deviation = -other
  def *(factor: Rational): Deviation = ZeroDev
}

/**
  Deviation with value defined by a constant.
 */
case class ConstantDev(i: Int, v: Rational) extends Deviation(i) {
  assert( v != Rational.zero, "ConstantDev with zero value")
  
  def value = v
  def unary_-(): Deviation = new ConstantDev(index, -v)
  
  def +(other: Deviation): Deviation = other match {
    case ZeroDev => this
    case ConstantDev(i2, v2) if (i == i2) => Deviation(i, v + v2)
    case _ =>
      throw MismatchedIndicesException("Index " + i + " does not match " + other.index)
      null
  }

  def -(other: Deviation): Deviation = other match {
    case ZeroDev => this
    case ConstantDev(i2, v2) if (i == i2) => Deviation(i, v - v2)
    case _ =>
      throw MismatchedIndicesException("Index " + i + " does not match " + other.index)
      null
  }

  def *(factor: Rational): Deviation = Deviation(i, v * factor)

}

object Utils {

  // TODO: fold
  def sumQueue(q: Queue[Deviation]): Rational = {
    var sum = Rational.zero
    val iter = q.iterator
    while(iter.hasNext) {
      sum += Rational.abs(iter.next.value)
    }
    sum
  }

  def addQueues(xn: Queue[Deviation], yn: Queue[Deviation]): Queue[Deviation] = {
    var deviation = new Queue[Deviation]()
    val iterX = xn.iterator
    val iterY = yn.iterator

    val fx = (xi: Deviation) => { deviation += xi; val x = 0 }
    val fy = (yi: Deviation) => { deviation += yi; val x = 0 }

    val fCouple = (xi: Deviation, yi: Deviation) => {
      val zi =  xi + yi
      zi match {
        case ZeroDev => ;
        case _ => deviation += zi
      }
      val x = 0  // TODO: can we get rid of this?
    }
    //println("addQueues")
    RationalDoubleQueueIterator.iterate(iterX, iterY, ZeroDev, fx, fy, fCouple)
    return deviation
  }

  def subtractQueues(xn: Queue[Deviation], yn: Queue[Deviation]): Queue[Deviation] = {
    var deviation = new Queue[Deviation]()
    val iterX = xn.iterator
    val iterY = yn.iterator

    val fx = (xi: Deviation) => { deviation += xi; val x = 0 }
    val fy = (yi: Deviation) => { deviation += -yi; val x = 0 }

    val fCouple = (xi: Deviation, yi: Deviation) => {
      val zi =  xi - yi
      zi match {
        case ZeroDev => ;
        case _ => deviation += zi
      }
      val x = 0
    }
    //println("subtractQueues")
    RationalDoubleQueueIterator.iterate(iterX, iterY,
      ZeroDev, fx, fy, fCouple)
    return deviation
  }

  def multiplyQueues(a: Rational, xqueue: Queue[Deviation], b: Rational,
    yqueue: Queue[Deviation]): Queue[Deviation] = {
    var deviation = new Queue[Deviation]()
    val iterX = xqueue.iterator
    val iterY = yqueue.iterator

    val fx = (dev: Deviation) => {
      val zi = dev * b
      zi match {
        case ZeroDev => ;
        case _ => deviation += zi
      }
      val x = 0
    }
    val fy = (dev: Deviation) => {
      val zi = dev * a
      zi match {
        case ZeroDev => ;
        case _ => deviation += zi
      }
      val x = 0
    }
    val fCouple = (xi: Deviation, yi: Deviation) => {
      val zi = xi * b + yi * a
      zi match {
        case ZeroDev => ;
        case _ => deviation += zi
      }
      val x = 0
    }
    //println("multiplyQueues")
    RationalDoubleQueueIterator.iterate(iterX, iterY,
      ZeroDev, fx, fy, fCouple)
    return deviation
  }

  def multiplyQueue(queue: Queue[Deviation], factor: Rational): Queue[Deviation] = {
    var deviation = new Queue[Deviation]()
    val iter = queue.iterator
    while(iter.hasNext) {
      val xi = iter.next
      val zi = xi * factor
      zi match {
        case ZeroDev => ;
        case _ => deviation += zi
      }
    }
    return deviation
  }

  def getIndices(q: Queue[Deviation]): collection.immutable.Set[Int] = {
    var i = 0
    var set = new collection.immutable.HashSet[Int]()
    while (i < q.size) {
      set += q(i).index
      i += 1
    }
    set
  }


}


object RationalDoubleQueueIterator {

  def iterate(iterX: Iterator[Deviation], iterY: Iterator[Deviation],
    dummy: Deviation, fx: (Deviation) => Unit, fy: (Deviation) => Unit,
    fCouple: (Deviation, Deviation) => Unit): Unit = {
    var xi: Deviation = if(iterX.hasNext) iterX.next else dummy
    var yi: Deviation = if(iterY.hasNext) iterY.next else dummy

    while(iterX.hasNext || iterY.hasNext) {
      if(xi.index < yi.index) {
        fx(xi)
        xi = if(iterX.hasNext) iterX.next else dummy
      }
      else if(yi.index < xi.index) {
        fy(yi)
        yi = if(iterY.hasNext) iterY.next else dummy
      }
      else {
        fCouple(xi, yi)
        xi = if(iterX.hasNext) iterX.next else dummy
        yi = if(iterY.hasNext) iterY.next else dummy
      }
    }
    if(xi.index == yi.index) {
      if(xi != dummy) {
        fCouple(xi, yi)
        xi = dummy
        yi = dummy
      }
    }
    else if(xi.index < yi.index) {
      if(xi != dummy) {fx(xi); xi = dummy}
      if(yi != dummy) {fy(yi); yi = dummy}
    }
    else if(yi.index < xi.index) {
      if(yi != dummy) {fy(yi); yi = dummy}
      if(xi != dummy) {fx(xi); xi = dummy}
    }
  }
}


