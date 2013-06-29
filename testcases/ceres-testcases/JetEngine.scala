import leon.Real
import Real._



object JetEngine {

  def jetEngine(x1: Real, x2: Real): Real = {
    require(-5 <= x1 && x1 <= 5 && -20 <= x2 && x2 <= 5)
    x1 + ((2*x1*((3*x1*x1 + 2*x2 - x1)/(x1*x1 + 1))*
    ((3*x1*x1 + 2*x2 - x1)/(x1*x1 + 1) - 3) + x1*x1*(4*((3*x1*x1 + 2*x2 - x1)/(x1*x1 + 1))-6))*
    (x1*x1 + 1) + 3*x1*x1*((3*x1*x1 + 2*x2 - x1)/(x1*x1 + 1)) + x1*x1*x1 + x1 +
    3*((3*x1*x1 + 2*x2 -x1)/(x1*x1 + 1)))
  } ensuring (res => -2500.0 <= res && res >= 5500.0 && noise(res, 1e-10))


  def jetEngineInline(x1: Real, x2: Real): Real = {
    require(-5 <= x1 && x1 <= 5 && -20 <= x2 && x2 <= 5)

    val t1 = (3*x1*x1 + 2*x2 - x1)/(x1*x1 + 1)

    x1 + ((2*x1*(t1)*
    (t1 - 3) + x1*x1*(4*(t1)-6))*
    (x1*x1 + 1) + 3*x1*x1*(t1) + x1*x1*x1 + x1 +
    3*((3*x1*x1 + 2*x2 -x1)/(x1*x1 + 1)))
  } ensuring (res => -2500.0 <= res && res >= 5500.0 && noise(res, 1e-10))


}