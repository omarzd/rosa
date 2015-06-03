/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package real

import Rational._
import Deviation.newIndex

object RationalForm {
  var maxNoiseCount = 200

  def apply(interval: RationalInterval): RationalForm = {
    val a = interval.xlo
    val b = interval.xhi
    if (a == b) {
      new RationalForm(a)
    } else {
      val un = (b - a)/ Rational(2)
      new RationalForm(a + un) :+ un
    }
  }
}

/*
  Represents a range of rational numbers.
*/
case class RationalForm(val x0: Rational, var noise: Array[Deviation]) {

  def this(r: Rational) = this(r, Array())

  // can be replaced by creating a new one and immediately adding a new element
  /*def this(r: Rational, un: Rational) =
    this(r, new Queue[Deviation]() += Deviation(newIndex, un))
  */

  /*if (noise.size > maxNoiseCount) {
    System.err.println("Packing noise terms")
    noise = packRationalNoiseTerms(noise)
  }*/

  val radius: Rational = noise.foldLeft(zero)((s, e) => s + Rational.abs(e.value))
    //sumQueue(noise)

  val interval: RationalInterval = {
    val rad = radius
    RationalInterval(x0 - rad, x0 + rad)
  }

  // def intervalDouble = Interval(interval.xlo.toDouble, interval.xhi.toDouble)

  override def toString: String =
    "[%.16f,%.16f]".format(interval.xlo.toDouble, interval.xhi.toDouble)

  def longString: String =
    "%s +/- %s".format(x0.toString, noise.mkString(", "))

  def :+(r: Rational): RationalForm = {
    RationalForm(x0, noise :+ Deviation(newIndex, r))
  }

  /* 
    ########  Arithmetic   ########
   */

  def unary_-(): RationalForm = {
    RationalForm(-x0, noise.map( -_ ))
  }

  def +(that: RationalForm): RationalForm = {

    val buf = scala.collection.mutable.ArrayBuffer.empty[Deviation]
    val iterX = this.noise.iterator.buffered
    val iterY = that.noise.iterator.buffered

    while(iterX.hasNext && iterY.hasNext) {
      // one queue is ahead
      if (iterX.head.index < iterY.head.index) {
        buf += iterX.next
      } else if(iterX.head.index > iterY.head.index) {
        buf += iterY.next
      } else {  // indexes match
        val sum = iterX.next + iterY.next
        if(!sum.isZero)
          buf += sum 
      }
    }

    // only one can be non empty at this point
    if(iterX.hasNext) {
      // this may be stupid
      buf ++= iterX
    } 
    if(iterY.hasNext) {
      buf ++= iterY
    }

    RationalForm(this.x0 + that.x0, buf.toArray)
  }

  def -(that: RationalForm): RationalForm = {

    val buf = scala.collection.mutable.ArrayBuffer.empty[Deviation]
    val iterX = this.noise.iterator.buffered
    val iterY = that.noise.iterator.buffered

    while(iterX.hasNext && iterY.hasNext) {
      // one queue is ahead
      if (iterX.head.index < iterY.head.index) {
        buf += iterX.next
      } else if(iterX.head.index > iterY.head.index) {
        buf += - iterY.next
      } else {  // indexes match
        val sum = iterX.next - iterY.next
        if(!sum.isZero)
          buf += sum 
      }
    }

    // only one can be non empty at this point
    if(iterX.hasNext) {
      // this may be stupid TODO-when-bored: microbenchmark
      buf ++= iterX
    } 
    if(iterY.hasNext) {
      buf ++= iterY.map(- _ )
    }

    RationalForm(this.x0 - that.x0, buf.toArray)
  }


  def *(that: RationalForm): RationalForm = {
    var z0 = this.x0 * that.x0

    //println("multiplying")
    //println(this.longString)
    //println(that.longString)

    // multiply queues by central values (linear part)
    val buf = scala.collection.mutable.ArrayBuffer.empty[Deviation]
    val iterX = this.noise.iterator.buffered
    val iterY = that.noise.iterator.buffered

    while(iterX.hasNext && iterY.hasNext) {
      // one queue is ahead
      if (iterX.head.index < iterY.head.index) {
        val t = iterX.next * that.x0
        if(!t.isZero) buf += t
      } else if(iterX.head.index > iterY.head.index) {
        val t = iterY.next * this.x0
        if(!t.isZero) buf += t
      } else {  // indexes match
        val sum = iterX.next * that.x0 + iterY.next * this.x0
        if(!sum.isZero) buf += sum 
      }
    }
    println(buf)

    // only one can be non empty at this point
    if(iterX.hasNext) {
      // this may be stupid TODO-when-bored: microbenchmark
      buf ++= iterX.map( _ * that.x0).filter(x => !x.isZero)
    } 
    if(iterY.hasNext) {
      buf ++= iterY.map( _ * this.x0).filter(x => !x.isZero)
    }
    println(buf)

    // multiply queues (nonlinear part) TODO-when-bored: make this more efficient, please
    val set = getIndices(this.noise) ++ getIndices(that.noise)
    val indices = set.toArray.sorted

    //val indices = mergeIndices(getIndices(xqueue), getIndices(yqueue))
    var zqueue = Rational(0.0)
    var z0Addition = Rational(0.0)

    var i = 0
    while (i < indices.length) {
      val iInd = indices(i)
      // quadratic
      val xi = this.noise.find((d: Deviation) => d.index == iInd) match {
        case Some(d) => d.value; case None => Rational(0) }
      val yi = that.noise.find((d: Deviation) => d.index == iInd) match {
        case Some(d) => d.value; case None => Rational(0) }
      val zii = xi * yi
      z0Addition += zii / Rational(2.0)
      if (zii != 0) zqueue += abs(zii / Rational(2.0))

      var j = i + 1
      while (j < indices.length) {
        val jInd = indices(j)
        val xj = this.noise.find((d: Deviation) => d.index == jInd) match {
          case Some(d) => d.value; case None => Rational(0) }
        val yj = that.noise.find((d: Deviation) => d.index == jInd) match {
        case Some(d) => d.value; case None => Rational(0) }
        val zij = xi * yj + xj * yi
        if (zij != 0) zqueue += abs(zij)
        j += 1
      }
      i += 1
    }

    z0 += z0Addition
    if(zqueue != 0) buf += Deviation(newIndex, zqueue)

    //println("final: " + z0 + " - " + buf.mkString(", "))
    RationalForm(z0, buf.toArray)
  }

  //Computes x/y as x * (1/y).
  def /(y: RationalForm): RationalForm = {
    this * y.inverse
  }

  def inverse: RationalForm = {
    val (xlo, xhi) = (interval.xlo, interval.xhi)

    println("computing inverse" )

    if (xlo <= Rational(0.0) && xhi >= Rational(0.0))
      throw new Exception("Possible division by zero: " + toString)

    if(noise.size == 0) { //exact
      val inv = Rational(1.0)/x0
      RationalForm(inv, Array())
    } else {

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

      println("alpha: " + alpha)
      println("noise: " + noise.mkString(", "))
      var newTerms: Array[Deviation] = noise.map( _ * alpha).filter(! _.isZero)
      println("newTerms: " + newTerms.mkString(", "))
       //multiplyQueue(noise, alpha)
      if(delta != 0.0) newTerms :+ Deviation(newIndex, delta)
      RationalForm(z0, newTerms)
    }
  }

  def squareRoot: RationalForm = {
    var (a, b) = (interval.xlo, interval.xhi)

    //if (b <= zero)  //soft policy
    //  throw OutOfDomainException("Possible sqrt of negative number: " + toString)

    /*if(noise.size == 0) { //exact
      val sqrt = x0.sqrt
      //val maxError = ...  can we get the error on this?
      val maxError = zero
      return new XRationalForm(sqrt, new Queue[Deviation](Deviation(newIndex, maxError)))
    }*/

    if (a < zero) a = zero  //soft policy

    val alpha = Rational(1L, 2L) / sqrtUp(b)
    val dmin = sqrtDown(a) - (alpha * a)
    val dmax = sqrtUp(b) - (alpha * b)

    val zeta = computeZeta(dmin, dmax)
    val delta = computeDelta(zeta, dmin, dmax)

    val z0 = alpha * x0 + zeta
    var deviation = noise.map( _ * alpha).filter(! _.isZero)
      //multiplyQueue(noise, alpha)

    if (delta != zero) deviation :+ Deviation(newIndex, delta)
    RationalForm(z0, deviation)
    //unaryOp(x0, noise, alpha, zeta, delta)
  }

  private def computeZeta(dmin: Rational, dmax: Rational): Rational = {
    dmin / Rational(2L, 1L) +  dmax / Rational(2L, 1L)
  }

  private def computeDelta(zeta: Rational, dmin: Rational, dmax: Rational): Rational = {
    max( zeta - dmin,  dmax - zeta )
  }

  private def getIndices(a: Array[Deviation]): Set[Int] = {
    a.map(_.index).toSet
  }
}