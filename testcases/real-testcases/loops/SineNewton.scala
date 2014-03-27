import leon.real._
import RealOps._
import annotations._

object SineNewton {

  def newton(x: Real, k: Int): Real = {
    require(loopCounter(k) && -1.0 < x && x < 1.0 && -1.0 < ~x && ~x < 1.0)

    if (k < 10) {
      newton(x - (x - (x°°3)/6.0 + (x°°5)/120.0 + (x°°7)/5040.0) / 
        (1 - (x*x)/2.0 + (x°°4)/24.0 + (x°°6)/720.0), k + 1)
    } else {
      x
    }
    
  } ensuring(res => -1.0 < x && x < 1.0 && -1.0 < ~x && ~x < 1.0)

  def newtonReal(x: Real, k: Int): Real = {
    require(loopCounter(k) && -1.0 < x && x < 1.0)

    if (k < 10) {
      newtonReal(x - (x - (x°°3)/6.0 + (x°°5)/120.0 + (x°°7)/5040.0) / 
        (1 - (x*x)/2.0 + (x°°4)/24.0 + (x°°6)/720.0), k + 1)
    } else {
      x
    }
    
  } ensuring(res => -1.0 < x && x < 1.0)  // has not diverged
  // This condition could probably be even stronger, something like 
  // ensuring( res => res < 0.1 * x)


  def newtonRealUnstable(x: Real, k: Int): Real = {
    require(loopCounter(k) && -1.2 < x && x < 1.2)

    if (k < 10) {
      newtonRealUnstable(x - (x - (x°°3)/6.0 + (x°°5)/120.0 + (x°°7)/5040.0) / 
        (1 - (x*x)/2.0 + (x°°4)/24.0 + (x°°6)/720.0), k + 1)
    } else {
      x
    }
    
  } ensuring(res => -1.2 < x && x < 1.2) 


  /*
  @loopbound(3)
  def newton(x: Real): Real = {
    require(-1.0 < x && x < 1.0)

    iterate(x) {
      x <== x - (x - (x°°3)/6.0 + (x°°5)/120.0 + (x°°7)/5040.0) / 
        (1 - (x*x)/2.0 + (x°°4)/24.0 + (x°°6)/720.0)
    }
  } ensuring (res => -1.0 < x && x < 1.0)

  @loopbound(3)
  def newtonUnstable(x: Real): Real = {
    require(-1.2 < x && x < 1.2)

    iterate(x) {
      x <== x - (x - (x°°3)/6.0 + (x°°5)/120.0 + (x°°7)/5040.0) / 
        (1 - (x*x)/2.0 + (x°°4)/24.0 + (x°°6)/720.0)
    }
  } ensuring (res => -1.2 < x && x < 1.2)
  */

  /*def newton(x: Real, i: Int): Real = {
    require(-1.0 < x && x < 1.0)

    if (i < 10) {
      newton(x - (x - (x*x*x)/6.0 + (x*x*x*x*x)/120.0 + (x*x*x*x*x*x*x)/5040.0) / 
        (1 - (x*x)/2.0 + (x*x*x*x)/24.0 + (x*x*x*x*x*x)/720.0), i + 1)
    } else {
      x
    }
    
  } ensuring(res => -1.0 < x && x < 1.0)  // has not diverged
  // This condition could probably be even stronger, something like 
  // ensuring( res => res < 0.1 * x)

  def newton2(x: Real): Real = {
    require(-1.2 < x && x < 1.2)

    if (i < 10) {
      newton2(x - (x - (x*x*x)/6.0 + (x*x*x*x*x)/120.0 + (x*x*x*x*x*x*x)/5040.0) / 
        (1 - (x*x)/2.0 + (x*x*x*x)/24.0 + (x*x*x*x*x*x)/720.0), i + 1)
    } else {
      x
    }
    
  } ensuring(res => -1.2 < x && x < 1.2)  // diverges (in some cases)!
  */
}