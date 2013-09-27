import leon.Real
import Real._


/*
  Source: http://www.lix.polytechnique.fr/Labo/Sylvie.Putot/Benchs/Modular/img_filter.c
  from paper: "Modular static analysis with Zonotopes"
*/
object Fluctuat {
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


//#############################

// The code is supposed to call these functions depending on the range
  // of the input, but the code never calls sin1, sin3 or sin4???

  // This would be a good benchmark for synthesizing those ranges

  def sin1(x: Real): Real = {
    require(x.in(-3.4, 3.4))
    val x2 = x*x
    ((-14.13341245 / (x2+41.17619681)+ 0.176575) * x2 + 1.0) * x
  }

  def sin2(x: Real): Real  = {
    require(x.in(-3.4, 3.4))
    val x2 = x*x
    (((-x2/(6.0*7)+1.0)*x2/(5.0*4)-1.0)*x2/(2.0*3)+1.0)*x
  }

  def sin3(x: Real): Real = {
    require(x.in(-3.4, 3.4))
    val x2 = x*x
    (x2/(x2/(x2/(x2/(x2/(-8.6822950335) +9.6717198021)+11.4544368439) + -3.3333337415) + -6.0000000056) + 1.0) * x
  }

  def sin4(x: Real): Real = {
    require(x.in(-3.4, 3.4))
    val SS_A0S = 1.0
    val SS_AS = (9.6717198021 * -8.6822950335 + -3.3333337415 * (11.4544368439 + -8.6822950335))
    val SS_BS = (-3.3333337415 * 11.4544368439 * 9.6717198021 * -8.6822950335)
    val SS_CS = (-6.0000000056 + 11.4544368439 + -8.6822950335)
    val SS_DS = (-6.0000000056 * -3.3333337415 * (11.4544368439 + -8.6822950335)+(-6.0000000056 +11.4544368439)*9.6717198021 * -8.6822950335)
    val SS_ES = (-6.0000000056 * -3.3333337415 * 11.4544368439 * 9.6717198021 * -8.6822950335)

    val x2 = x*x
    ((((x2+SS_AS)*x2+SS_BS)*x2) /((SS_CS*x2+SS_DS)*x2+SS_ES)+SS_A0S)*x
  }

}
}