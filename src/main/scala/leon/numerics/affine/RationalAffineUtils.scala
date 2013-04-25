package leon.numerics.affine

import ceres.common._
import Rational._

import collection.mutable.Queue

case class DivisionByZeroException(s: String) extends Exception
case class MismatchedException(msg: String) extends Exception(msg)

object Deviation {
  var currIndex: Int = 0
  def newIndex: Int = {
    currIndex += 1
    assert(currIndex != Int.MaxValue, "Affine indices just ran out...")
    currIndex
  }

  

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
  def unary_-(): Deviation = ConstantDev(index, -v)
  
  def +(other: Deviation): Deviation = other match {
    case ZeroDev => this
    case ConstantDev(i2, v2) if (i == i2) => Deviation(i, v + v2)
    case _ =>
      throw MismatchedException("Indices or types don't match.")
      null
  }

  def -(other: Deviation): Deviation = other match {
    case ZeroDev => this
    case ConstantDev(i2, v2) if (i == i2) => Deviation(i, v - v2)
    case _ =>
      throw MismatchedException("Indices or types don't match.")
      null
  }

  def *(factor: Rational): Deviation = Deviation(i, v * factor)

}

/**
  Keeps track of it's history, ie which initial indices it has been computed from.
  @param history list of indices of noise terms this one has been computed from
  For example, if you multiply x1e1 * x2e2 = (x1*x2)*e3 [1,2].
  Multiple indices are possible, [1,1] for example stands for e1*e1.
  We don't do this for all inputs and uncertainties, as we only interested in those
  from inputs.
 */
case class VariableDev(i: Int, v: Rational, history: List[Int]) extends Deviation(i) {
  //assert( v != Rational.zero, "VariableDev with zero value, index " + history)
  // TODO: can go to abstract class
  def value: Rational = v

  def unary_-(): Deviation = VariableDev(index, -v, history)
  
  def +(other: Deviation): Deviation = other match {
    case ZeroDev => this
    case VariableDev(i2, v2, h2) if (index == i2 && history == h2) =>
      VariableDev(index, v + v2, history)
    case _ => throw MismatchedException("Indices or types don't match.")
      null
  }

  def -(other: Deviation): Deviation = other match {
    case ZeroDev => this
    case VariableDev(i2, v2, h2) if (index == i2 && history == h2) =>
      VariableDev(index, v - v2, history)
    case _ => throw MismatchedException("Indices or types don't match.")
      null
  }

  def *(factor: Rational): Deviation = {
    VariableDev(index, v * factor, history)
  }

  override def toString: String = value.toDouble.toString + "f" + index + "[" +history+"]"
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

  def multiplyNonlinearQueues(xqueue: Queue[Deviation], yqueue: Queue[Deviation]): Rational = {
    val indices = mergeIndices(getIndices(xqueue), getIndices(yqueue))
    var zqueue = Rational(0.0)

    var i = 0
    while (i < indices.length) {
      val iInd = indices(i)
      // quadratic
      val xi = xqueue.find((d: Deviation) => d.index == iInd) match {
        case Some(d) => d.value; case None => Rational(0) }
      val yi = yqueue.find((d: Deviation) => d.index == iInd) match {
        case Some(d) => d.value; case None => Rational(0) }
      val zii = xi * yi
      if (zii != 0) zqueue += abs(zii)

      var j = i + 1
      while (j < indices.length) {
        val jInd = indices(j)
        val xj = xqueue.find((d: Deviation) => d.index == jInd) match {
        case Some(d) => d.value; case None => Rational(0) }
        val yj = yqueue.find((d: Deviation) => d.index == jInd) match {
        case Some(d) => d.value; case None => Rational(0) }
        val zij = xi * yj + xj * yi
        if (zij != 0) zqueue += abs(zij)
        j += 1
      }
      i += 1
    }
    zqueue
  }

  // Does a smarter computation of the quadratic terms
  def multiplyNonlinearQueues2(xqueue: Queue[Deviation], yqueue: Queue[Deviation]): (Rational, Rational) = {
    val indices = mergeIndices(getIndices(xqueue), getIndices(yqueue))
    var zqueue = Rational(0.0)
    var z0Addition = Rational(0.0)

    var i = 0
    while (i < indices.length) {
      val iInd = indices(i)
      // quadratic
      val xi = xqueue.find((d: Deviation) => d.index == iInd) match {
        case Some(d) => d.value; case None => Rational(0) }
      val yi = yqueue.find((d: Deviation) => d.index == iInd) match {
        case Some(d) => d.value; case None => Rational(0) }
      val zii = xi * yi
      z0Addition += zii / Rational(2.0)
      if (zii != 0) zqueue += abs(zii / Rational(2.0))

      var j = i + 1
      while (j < indices.length) {
        val jInd = indices(j)
        val xj = xqueue.find((d: Deviation) => d.index == jInd) match {
          case Some(d) => d.value; case None => Rational(0) }
        val yj = yqueue.find((d: Deviation) => d.index == jInd) match {
        case Some(d) => d.value; case None => Rational(0) }
        val zij = xi * yj + xj * yi
        if (zij != 0) zqueue += abs(zij)
        j += 1
      }
      i += 1
    }
    (z0Addition, zqueue)
  }


  private def mergeIndices(x: Set[Int], y: Set[Int]): Array[Int] = {
    val set = x ++ y
    val list = set.toList.sorted
    return list.toArray
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


