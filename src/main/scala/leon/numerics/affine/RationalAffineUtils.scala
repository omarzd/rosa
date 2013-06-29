package leon.numerics.affine

import ceres.common._
import Rational._

import collection.mutable.Queue
import Deviation._


object Utils {

  // Until we get this sorted in Rational
  // TODO: check this
  def sqrtUp(x: Rational): Rational = Rational(DirectedRounding.sqrtUp(Rational.scaleToIntsUp(x).doubleValue))
  def sqrtDown(x: Rational): Rational = Rational(DirectedRounding.sqrtDown(Rational.scaleToIntsDown(x).doubleValue))

  def computeZeta(dmin: Rational, dmax: Rational): Rational = {
    dmin / Rational(2l, 1l) +  dmax / Rational(2l, 1l)
  }

  def computeDelta(zeta: Rational, dmin: Rational, dmax: Rational): Rational = {
    max( zeta - dmin,  dmax - zeta )
  }

  def unaryOp(x0: Rational, noise: Queue[Deviation], alpha: Rational, zeta: Rational,
    delta: Rational) : XRationalForm = {

    val z0 = alpha * x0 + zeta
    var deviation = multiplyQueue(noise, alpha)

    if (delta != zero) deviation += Deviation(newIndex, delta)
    return new XRationalForm(z0, deviation)
  }


  def sumQueue(q: Queue[Deviation]): Rational = {
    var sum = Rational.zero
    val iter = q.iterator
    while(iter.hasNext) {
      sum += Rational.abs(iter.next.value)
    }
    sum
  }

  def sumSeq(q: Seq[Deviation]): Rational = {
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
      val x = 0
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

  /*def multiplyNonlinearQueues(xqueue: Queue[Deviation], yqueue: Queue[Deviation]): Rational = {
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
  }*/

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

  /**
    We cannot use the iterators above because they will miss the
    (x1*y2 + x2*y2)e1e2 relationship
    @return (queue, error) queue of VarDevs and the remaining errors
   */
  /*def multiplyNonlinearQueuesWithDependencies(xqueue: Queue[Deviation], yqueue: Queue[Deviation]):
    (Queue[Deviation], Rational) = {
    val indices = mergeIndices(getIndices(xqueue), getIndices(yqueue))
    var zqueue = new Queue[Deviation]()
    var zerror = Rational.zero

    var i = 0
    while (i < indices.length) {
      val iInd = indices(i)
      // quadratic
      val xi: Deviation = xqueue.find((d: Deviation) => d.index == iInd) match {
        case Some(d) => d; case None => dummyDev }
      val yi: Deviation = yqueue.find((d: Deviation) => d.index == iInd) match {
        case Some(d) => d; case None => dummyDev }
      val zii = xi * yi
      if (!zii.isZero) {
        zii match {
          case VariableDev(i, v, h) => zqueue += zii
          case _ => zerror += abs(zii.value)
        }
      }

      var j = i + 1
      while (j < indices.length) {
        val jInd = indices(j)
        val xj = xqueue.find((d: Deviation) => d.index == jInd) match {
          case Some(d) => d; case None => dummyDev }
        val yj = yqueue.find((d: Deviation) => d.index == jInd) match {
        case Some(d) => d; case None => dummyDev }
        val zij = xi * yj + xj * yi
        if (!zij.isZero) {
          zij match {
            case VariableDev(i, v, h) => zqueue += zij
            case _ => zerror += abs(zij.value)
          }
        }
        j += 1
      }
      i += 1
    }
    (zqueue, zerror)
  }*/



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


