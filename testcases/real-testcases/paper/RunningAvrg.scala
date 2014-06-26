import leon.real._
import RealOps._
import annotations._


object RunningAvrg {

  @model
  def nextItem: Real = { 
    ????
  } ensuring (res => -1200 <= res && res <= 1200 && res +/- 1e-8)

  def mean(n: Int, m: Real): Real = {
    require(-1200 <= m && m <= 1200 && 2 <= n && n <= 1002 &&
      -1200.5 <= ~m && ~m <= 1200.5)

    if (n < 102) {

      val x = nextItem

      val m_new = ((n - 1.0) * m + x) / n
      mean(n + 1, m_new)
      
    } else {
      m
    }
    
  } ensuring (res => -1200.00 <= res && res <= 1200.00)

}