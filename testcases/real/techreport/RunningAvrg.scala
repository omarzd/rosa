import leon.real._
import RealOps._
import annotations._


object RunningAvrg {

  @model
  def nextItem: Real = { 
    ????
  } ensuring (res => -1200 <= res && res <= 1200 && res +/- 1e-8)

  def mean100(n: Int, m: Real): Real = {
    require(-1200 <= m && m <= 1200 && 2 <= n && n <= 1002 &&
      -1200.5 <= ~m && ~m <= 1200.5)

    if (n < 102) {

      val x = nextItem

      val m_new = ((n - 1.0) * m + x) / n
      mean100(n + 1, m_new)
      
    } else {
      m
    }
    
  } ensuring (res => -1200.00 <= res && res <= 1200.00)


  def mean500(n: Int, m: Real): Real = {
    require(-1200 <= m && m <= 1200 && 2 <= n && n <= 1002 &&
      -1200.5 <= ~m && ~m <= 1200.5)

    if (n < 502) {

      val x = nextItem

      val m_new = ((n - 1.0) * m + x) / n
      mean500(n + 1, m_new)
      
    } else {
      m
    }
    
  } ensuring (res => -1200.00 <= res && res <= 1200.00)


  def mean1000(n: Int, m: Real): Real = {
    require(-1200 <= m && m <= 1200 && 2 <= n && n <= 1002 &&
      -1200.5 <= ~m && ~m <= 1200.5)

    if (n < 1002) {

      val x = nextItem

      val m_new = ((n - 1.0) * m + x) / n
      mean1000(n + 1, m_new)
      
    } else {
      m
    }
    
  } ensuring (res => -1200.00 <= res && res <= 1200.00)

  def mean2000(n: Int, m: Real): Real = {
    require(-1200 <= m && m <= 1200 && 2 <= n && n <= 1002 &&
      -1200.5 <= ~m && ~m <= 1200.5)

    if (n < 2002) {

      val x = nextItem

      val m_new = ((n - 1.0) * m + x) / n
      mean2000(n + 1, m_new)
      
    } else {
      m
    }
    
  } ensuring (res => -1200.00 <= res && res <= 1200.00)


  def mean3000(n: Int, m: Real): Real = {
    require(-1200 <= m && m <= 1200 && 2 <= n && n <= 1002 &&
      -1200.5 <= ~m && ~m <= 1200.5)

    if (n < 3002) {

      val x = nextItem

      val m_new = ((n - 1.0) * m + x) / n
      mean3000(n + 1, m_new)
      
    } else {
      m
    }
    
  } ensuring (res => -1200.00 <= res && res <= 1200.00)


  def mean4000(n: Int, m: Real): Real = {
    require(-1200 <= m && m <= 1200 && 2 <= n && n <= 1002 &&
      -1200.5 <= ~m && ~m <= 1200.5)

    if (n < 4002) {

      val x = nextItem

      val m_new = ((n - 1.0) * m + x) / n
      mean4000(n + 1, m_new)
      
    } else {
      m
    }
    
  } ensuring (res => -1200.00 <= res && res <= 1200.00)

}
