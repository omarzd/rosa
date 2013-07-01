

import leon.Real
import Real._

import leon.Utils._

object Mult {

  def mult(a: Real, b: Real): Real = {
    require(a.in(-1.0, 2.0) && b.in(-2.0, 2.0))
    a * (b - 2)
  }

  def compute(x: Real): Real = {
    require(x.in(-1.0, 1.0))
    val y1 = mult(x+1, x)
    val y2 = mult(x, 2*x)
    y2 - y1
  } ensuring(res => noise(res, 1e-5))


/*int N = 100, i;
int main(...) {
  double x ∈ [−1,1];
  double y1, y2;
  for (i=0; i<N; i++) {
    y1 = mult(x+1,x);
    y2 = mult(x, 2*x);
    x /= 2;
  }
}*/
}