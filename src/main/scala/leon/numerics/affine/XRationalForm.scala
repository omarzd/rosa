package leon
package numerics.affine

import purescala.Trees._
import ceres.common.{Rational, RationalInterval, Interval}
import Rational._
import XRationalForm._
import collection.mutable.Queue

import Utils._
import Deviation._


//case class DivisionByZeroException(s: String) extends Exception
case class OutOfDomainException(s: String) extends Exception


object XRationalForm {
  var maxNoiseCount = 200

  def apply(interval: RationalInterval): XRationalForm = {
    val a = interval.xlo
    val b = interval.xhi
    val un = (b - a)/ Rational(2)
    new XRationalForm(a + un, un)
  }

  // This is the equivalent of adding [-a, a]
  def addNoise(x: XRationalForm, n: Rational): XRationalForm = {
    val newTerms = new Queue[Deviation]()
    var iter = x.noise.iterator
    while(iter.hasNext) {
      newTerms += iter.next
    }
    newTerms += Deviation(newIndex, n)
    new XRationalForm(x.x0, newTerms)
  }

  def addNoiseWithIndex(x: XRationalForm, n: Rational):
    (XRationalForm, Int) = {
    val newTerms = new Queue[Deviation]()
    var iter = x.noise.iterator
    while(iter.hasNext) {
      newTerms += iter.next
    }
    val index = newIndex
    newTerms += Deviation(index, List(index), n)
    (new XRationalForm(x.x0, newTerms), index)
  }

}

/*
  Represents a range of rational numbers.
*/
case class XRationalForm(val x0: Rational, var noise: Queue[Deviation]) {

  // Constant value
  def this(r: Rational) = this(r, new Queue[Deviation])

  // Creating a range of values in fixed point format
  def this(r: Rational, un: Rational) =
    this(r, new Queue[Deviation]() += Deviation(newIndex, un))

  if (noise.size > maxNoiseCount) {
    System.err.println("Packing noise terms")
    noise = packRationalNoiseTerms(noise)
  }

  val radius: Rational = sumQueue(noise)

  /** This is the interval of values in R represented by this fixed-point range. */
  val interval: RationalInterval = {
    val rad = radius
    RationalInterval(x0 - rad, x0 + rad)
  }

  def intervalDouble = Interval(interval.xlo.toDouble, interval.xhi.toDouble)

  override def toString: String =
    "[%.16f,%.16f]".format(intervalDouble.xlo, intervalDouble.xhi)

  def longString: String =
    "%s +/- %s".format(x0.toString, noise.toString)

  def absValue: XRationalForm = {
    if (Rational(0) <= x0) return this else return -this
  }

  def isNonZero: Boolean = return (x0 != 0 || noise.size > 0)

  /**
    Negates this XRationalForm.
   */
  def unary_-(): XRationalForm = {
    var newTerms = new Queue[Deviation]()
    var iter = noise.iterator
    while(iter.hasNext) {
      newTerms += - iter.next  // just flip the sign
    }
    new XRationalForm(-x0, newTerms)
  }


  def +(y: XRationalForm): XRationalForm =
    return new XRationalForm(this.x0 + y.x0, addQueues(this.noise, y.noise))

  def -(y: XRationalForm): XRationalForm =
    return new XRationalForm(this.x0 - y.x0, subtractQueues(this.noise, y.noise))

  def *(y: XRationalForm): XRationalForm = {
    var z0 = this.x0 * y.x0

    //var (zqueue, delta) =
    //  multiplyNonlinearQueuesWithDependencies(this.noise, y.noise)
    var (z0Addition, delta) = multiplyNonlinearQueues2(this.noise, y.noise)
    z0 += z0Addition
    //var delta = computeEta(this.noise, y.noise)

    //println("zqueue tyep: " + zqueue.getClass)
    var newTerms: Queue[Deviation] = multiplyQueues(this.x0, this.noise, y.x0, y.noise)
    //newTerms = newTerms ++ zqueue
    //val sortedNewTerms: Queue[Deviation] = newTerms.sortBy(x => x.index)
    if(delta != 0)
      newTerms += Deviation(newIndex, delta)
    return new XRationalForm(z0, newTerms)
  }

  /**
    Computes the inverse of this XRationalForm as a linear approximation.
   */
  def inverse: XRationalForm = {
    val (xlo, xhi) = (interval.xlo, interval.xhi)

    if (xlo <= Rational(0.0) && xhi >= Rational(0.0))
      throw OutOfDomainException("Possible division by zero: " + toString)

    if(noise.size == 0) { //exact
      val inv = Rational(1.0)/x0
      return new XRationalForm(inv, new Queue[Deviation]())
    }

    /* Calculate the inverse */
    val a = min(abs(xlo), abs(xhi))
    val b = max(abs(xlo), abs(xhi))

    val alpha = Rational(-1.0) / (b * b)

    val dmax = (Rational(1.0) / a) - (alpha * a)
    val dmin = (Rational(1.0) / b) - (alpha * b)

    var zeta = (dmin / Rational(2.0)) + (dmax / Rational(2.0))
    if (xlo < Rational(0.0)) zeta = -zeta
    val delta = max( zeta - dmin, dmax - zeta )

    val z0 = alpha * this.x0 + zeta

    var newTerms = multiplyQueue(noise, alpha)
    if(delta != 0.0) newTerms += Deviation(newIndex, delta)
    return new XRationalForm(z0, newTerms)
  }

  /**
   Computes x/y as x * (1/y).
   */
  def /(y: XRationalForm): XRationalForm = {
    return this * y.inverse
  }


  def squareRoot: XRationalForm = {
    var (a, b) = (interval.xlo, interval.xhi)

    if (b <= zero)  //soft policy
      throw OutOfDomainException("Possible sqrt of negative number: " + toString)

    /*if(noise.size == 0) { //exact
      val sqrt = x0.sqrt
      //val maxError = ...  can we get the error on this?
      val maxError = zero
      return new XRationalForm(sqrt, new Queue[Deviation](Deviation(newIndex, maxError)))
    }*/

    if (a < zero) a = zero  //soft policy

    val alpha = Rational(1l, 2l) / sqrtUp(b)
    val dmin = sqrtDown(a) - (alpha * a)
    val dmax = sqrtUp(b) - (alpha * b)

    val zeta = computeZeta(dmin, dmax)
    val delta = computeDelta(zeta, dmin, dmax)
    return unaryOp(x0, noise, alpha, zeta, delta)
  }



  private def packRationalNoiseTerms(queue: Queue[Deviation]): Queue[Deviation] = {
    var sum = sumQueue(queue)
    val avrg: Double = sum.toDouble / queue.size

    //compute st. deviation
    var devSum = 0.0
    val iter = queue.iterator
    while(iter.hasNext) {
      val diff = (abs(iter.next.value).toDouble - avrg).toDouble
      devSum += diff * diff
    }
    val stdDev = math.sqrt(devSum/queue.size)
    val threshold: Double = avrg + stdDev

    //Now compute the new queue
    var newNoise = Rational(0)
    var newDev = new Queue[Deviation]()

    val iter2 = queue.iterator
    while(iter2.hasNext) {
      val xi = iter2.next
      val v = abs(xi.value)
      if(v.toDouble < threshold) newNoise += v
      else newDev += xi
    }
    newDev += Deviation(newIndex, newNoise)
    return newDev
  }


/*private def multiplyNonlinearQueues(xqueue: Queue[Deviation], yqueue: Queue[Deviation]): Rational = {
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
  private def multiplyNonlinearQueues2(xqueue: Queue[Deviation], yqueue: Queue[Deviation]): (Rational, Rational) = {
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
  }*/
}
