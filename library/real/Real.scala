package leon.real
import leon.annotation._

import scala.language.implicitConversions

import scala.math.{ScalaNumericConversions, ScalaNumber}

import scala.annotation.StaticAnnotation

@leon.annotation.ignore
object annotations {
  class loopbound(max: Int) extends StaticAnnotation
  class model extends StaticAnnotation
  class robust extends StaticAnnotation
}

object RealOps {
    @proxy
    implicit def double2real(d: Double): Real = Real(d)

    @proxy
    implicit def int2real(i: Int): Real = Real(i.toDouble)

    @proxy
    def sqrt(x: Real): Real = ???

    @proxy
    def initialErrors(x: Boolean): Boolean = ???

    @ignore
    def iterate(x: Real)(updateFnc: Boolean): Real = ???

    @ignore
    def iterate(x1: Real, x2: Real)(
        updateFnc: Boolean): (Real, Real) = ???
    @ignore
    def iterate(x1: Real, x2: Real, x3: Real)(
        updateFnc: Boolean): (Real, Real, Real) = ???
    @ignore
    def iterate(x1: Real, x2: Real, x3: Real, x4: Real)(
        updateFnc: Boolean): (Real, Real, Real, Real) = ???
    @ignore
    def iterate(x1: Real, x2: Real, x3: Real, x4: Real, x5: Real)(
        updateFnc: Boolean): (Real, Real, Real, Real, Real) = ???
    @ignore
    def iterate(x1: Real, x2: Real, x3: Real, x4: Real, x5: Real, x6: Real)(
        updateFnc: Boolean): (Real, Real, Real, Real, Real, Real) = ???
    
    /*def iterate(x1: Real, x2: Real, x3: Real, x4: Real, x5: Real, x6: Real, x7: Real)(
        updateFnc: Boolean): (Real, Real, Real, Real, Real, Real, Real) = ???
    def iterate(x1: Real, x2: Real, x3: Real, x4: Real, x5: Real, x6: Real, x7: Real, x8: Real)(
        updateFnc: Boolean): (Real, Real, Real, Real, Real, Real, Real, Real) = ???
    def iterate(x1: Real, x2: Real, x3: Real, x4: Real, x5: Real, x6: Real, x7: Real, x8: Real, x9: Real)(
        updateFnc: Boolean): (Real, Real, Real, Real, Real, Real, Real, Real, Real) = ???
    def iterate(x1: Real, x2: Real, x3: Real, x4: Real, x5: Real, x6: Real, x7: Real, x8: Real, x9: Real, x10: Real)(
        updateFnc: Boolean): (Real, Real, Real, Real, Real, Real, Real, Real, Real, Real) = ???
    def iterate(x1: Real, x2: Real, x3: Real, x4: Real, x5: Real, x6: Real, x7: Real, x8: Real, x9: Real, x10: Real, x11: Real)(
        updateFnc: Boolean): (Real, Real, Real, Real, Real, Real, Real, Real, Real, Real, Real) = ???
    */
    
    // dummy value when we need to return something
    @proxy
    def ????(): Real = ???
}

@ignore
case class LoopCounter {

  def <(i: Int): Boolean = ???
  def ++(): LoopCounter = ???

}

@ignore
case class Real private[real](v: Double) extends ScalaNumber with ScalaNumericConversions with Ordered[Real] {
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