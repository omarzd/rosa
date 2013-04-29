package leon.numerics.affine

import ceres.common._
import Rational._

import collection.mutable.Queue
import Deviation._


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
      if (!zi.isZero) deviation += zi
      val x = 0  // TODO: can we get rid of this?
    }
    //println("addQueues")
    RationalDoubleQueueIterator.iterate(iterX, iterY, dummyDev, fx, fy, fCouple)
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
      if (!zi.isZero) deviation += zi
      val x = 0
    }
    //println("subtractQueues")
    RationalDoubleQueueIterator.iterate(iterX, iterY, dummyDev, fx, fy, fCouple)
    return deviation
  }

  def multiplyQueues(a: Rational, xqueue: Queue[Deviation], b: Rational,
    yqueue: Queue[Deviation]): Queue[Deviation] = {
    var deviation = new Queue[Deviation]()
    val iterX = xqueue.iterator
    val iterY = yqueue.iterator

    val fx = (dev: Deviation) => {
      val zi = dev * b
      if (!zi.isZero) deviation += zi
      val x = 0
    }
    val fy = (dev: Deviation) => {
      val zi = dev * a
      if (!zi.isZero) deviation += zi
      val x = 0
    }
    val fCouple = (xi: Deviation, yi: Deviation) => {
      val zi = xi * b + yi * a
      if (!zi.isZero) deviation += zi
      val x = 0
    }
    //println("multiplyQueues")
    RationalDoubleQueueIterator.iterate(iterX, iterY, dummyDev, fx, fy, fCouple)
    return deviation
  }

  def multiplyQueue(queue: Queue[Deviation], factor: Rational): Queue[Deviation] = {
    var deviation = new Queue[Deviation]()
    val iter = queue.iterator
    while(iter.hasNext) {
      val xi = iter.next
      val zi = xi * factor
      if (!zi.isZero) deviation += zi
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


