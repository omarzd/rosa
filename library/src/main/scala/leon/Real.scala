package leon

import scala.math.{ScalaNumericConversions, ScalaNumber}

  object Real {
    class NotExecutableException(msg: String) extends Exception
    private val exMsg = "don't know how to implement reals"

    //def ~(x: Real): Real = { throw new NotExecutableException(exMsg); null }

    implicit def double2real(d: Double): Real = new Real(d)
    implicit def int2real(i: Int): Real = new Real(i.toDouble)

    // This means |x - x0| <= n, note the less EQUALS.
    def noise(x: Real, n: Double): Boolean = { throw new NotExecutableException(exMsg); false }
    // Short for saying only the regular roundoff
    def roundoff(x: Real): Boolean = { throw new NotExecutableException(exMsg); false }

    //def uncertainty(x: Real): Real = { throw new NotExecutableException(exMsg); null }
    
    //def in(a: Real, b: Real): Boolean = { throw new NotExecutableException(exMsg); null }
  }

  class Real private(v: Double) extends ScalaNumber with ScalaNumericConversions with Ordered[Real] {
    import Real._

    def unary_-(): Real = { throw new NotExecutableException(exMsg); null }
    def +(other: Real): Real = { throw new NotExecutableException(exMsg); null }
    def -(other: Real): Real = { throw new NotExecutableException(exMsg); null }
    def *(other: Real): Real = { throw new NotExecutableException(exMsg); null }
    def /(other: Real): Real = { throw new NotExecutableException(exMsg); null }

    def compare(other: Real): Int = {
      throw new NotExecutableException(exMsg)
      0
    }

    def underlying(): AnyRef = this
    def isWhole(): Boolean = { throw new NotExecutableException(exMsg); false }
    def doubleValue(): Double = { throw new NotExecutableException(exMsg); 0.0 }
    def floatValue(): Float = { throw new NotExecutableException(exMsg); 0.0f }
    def longValue(): Long = { throw new NotExecutableException(exMsg); 0l }
    def intValue(): Int = { throw new NotExecutableException(exMsg); 0 }
  }
