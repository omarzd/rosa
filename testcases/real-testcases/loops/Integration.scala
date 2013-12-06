/*
These benchmarks are inspired from the 
FEVS - Functional Equivalence Verification Suite
vsl.cis.udel.edu/fevs
*/

/* integral_seq.c: numerical integration of function of a single variable.
 * Algorithm works on list of "interval" structures.  Each interval specifies
 * a little interval [a,b] the stores the values (b-a)*f(a) (left area), 
 * (b-a)*f(b) (right area), and the desired tolerance for that interval.
 * If abs(leftArea-rightArea)<=tolerance, the interval is considered "converged"
 * and the estimated integral of the interval is returned as the average of
 * leftArea and rightArea.  If the the interval is not converged, it is split,
 * i.e., replaced by two intervals by cutting [a,b] in half, and cutting
 * the tolerance in half. 
 *  */
// This is taken from the FEVS Functional Equivalence Verification Suite

object Integration {

  

// Recursive integration with the trapezoid rule.
  // In the original benchmark f was sin or cos and the interval of
  // integration [0, pi]
  def integrate(a: Real, b: Real, fa: Real, fb: Real, area: Real,
    tolerance: Real, f: Real => Real) {
    val delta = b - a
    val c = a + delta/2.0
    val fc = f(c)
    val leftArea = (fa + fc) * delta/4.0
    val rightArea = (fc + fb) * delta/4.0

    if (tolerance < epsilon) {
      leftArea + rightArea
    } else if (abs(leftArea + rightArea - area) <= tolerance) {
      leftArea + rightArea
    } else {
      integrate(a, c, fa, fc, leftArea, tolerance/2.0, f) +
      integrate(c, b, fc, fb, rightArea, tolerance/2.0, f)
    }
  }

}

/* 
Original:
double epsilon = DBL_MIN*10;
double pi = M_PI;
int count = 0;

double f1(double x) { return sin(x); }

double f2(double x) { return cos(x); }

double integrate(double a, double b, double fa, double fb, double area,
     double tolerance, double f(double)) {
  double delta = b - a;
  double c = a+delta/2;
  double fc = f(c);
  double leftArea = (fa+fc)*delta/4;
  double rightArea = (fc+fb)*delta/4;

  count++;
  if (tolerance < epsilon) {
    printf("Tolerance may not be possible to obtain.\n");
    return leftArea+rightArea;
  }
  if (fabs(leftArea+rightArea-area)<=tolerance) {
    return leftArea+rightArea;
  }
  return integrate(a, c, fa, fc, leftArea, tolerance/2, f) +
    integrate(c, b, fc, fb, rightArea, tolerance/2, f);
}

double integral(double a, double b, double tolerance, double f(double)) {
  count = 0;
  return integrate(a, b, f(a), f(b), (f(a)+f(b))*(b-a)/2, tolerance, f);
}

int main(int argc, char *argv[]) {
  printf("%4.20lf\n", integral(0, pi, .0000000001, f1));
  printf("%4.20lf\n", integral(0, pi, .0000000001, f2));
  return 0;
}
*/