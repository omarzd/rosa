package leon

import scala.language.implicitConversions

import scala.math.{ScalaNumericConversions, ScalaNumber}

  object Real {
    implicit def double2real(d: Double): Real = new Real(d)
    implicit def int2real(i: Int): Real = new Real(i.toDouble)

    def sqrt(x: Real): Real = ???

    def iterate(updateFnc: Boolean): (Real, Real) = ??? 
  }

  class Real private(v: Double) extends ScalaNumber with ScalaNumericConversions with Ordered[Real] {
    import Real._

    def unary_-(): Real = ???
    def +(other: Real): Real = ???
    def -(other: Real): Real = ???
    def *(other: Real): Real = ???
    def /(other: Real): Real = ???

    def unary_~(): Real = ???

    // Uncertainty on this value
    def +/-(x: Real): Boolean = ???
    def ±(x: Real): Boolean = ???

    def compare(other: Real): Int = ???

    def underlying(): AnyRef = this
    def isWhole(): Boolean = ???
    def doubleValue(): Double = ???
    def floatValue(): Float = ???
    def longValue(): Long = ???
    def intValue(): Int = ???

    /*
        The following are in an experimental state.
    */

    // Convenience method to specify intervals
    //def in(a: Real, b: Real): Boolean = { throw new NotExecutableException(exMsg); false }
    def ><(a: (Real, Real)): Boolean = ???

    def ^(power: Int): Real = ???
    def °(power: Int): Real = ???
    def °°(power: Int): Real = ???

    def ∈(bounds: (Real, Real)): Boolean = ???
    def ∈=(bounds: (Real, Real)): Boolean = ???

    // Error of this value
    def unary_!(): Real = ???

      
    def <==(rhs: Real): Boolean = ???
    def <--(rhs: Real): Boolean = ???
  }
