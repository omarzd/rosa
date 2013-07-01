
import leon.Real
import Real._

object Filter {

  def unroll1(a1: Real, a2: Real, a3: Real, b1: Real, b2: Real, e: Real, e0: Real, e1: Real): Real = {
    require(a1.in(0.5, 0.8) && a2.in(-1.5, -1.0) && a3.in(0.8, 1.3) && b1.in(1.39, 1.41) && b2.in(-0.71, -0.69) &&
      e.in(0.0, 1.0) && e0.in(0.0, 1.0) && e1.in(0.0, 1.0))

    val s0 = 0.0
    val s1 = 0.0

    val s = a1 * e + e0 * a2 + e1 * a3 + s0 * b1 + s1 * b2
    s
  } ensuring(res => res <= 20.0 && noise(res, 1e-13))


  def unroll10(a1: Real, a2: Real, a3: Real, b1: Real, b2: Real, e: Real, e0: Real, e1: Real, e2: Real,
    e3: Real, e4: Real, e5: Real, e6: Real, e7: Real, e8: Real, e9: Real): Real = {
    require(a1.in(0.5, 0.8) && a2.in(-1.5, -1.0) && a3.in(0.8, 1.3) && b1.in(1.39, 1.41) && b2.in(-0.71, -0.69) &&
      e.in(0.0, 1.0) && e0.in(0.0, 1.0) && e1.in(0.0, 1.0)&& e2.in(0.0, 1.0)&& e3.in(0.0, 1.0)&& e4.in(0.0, 1.0)&& e5.in(0.0, 1.0)&&
      e6.in(0.0, 1.0)&& e7.in(0.0, 1.0)&& e8.in(0.0, 1.0)&& e9.in(0.0, 1.0))

    val s0 = 0.0
    val s1 = 0.0

    val s2 = e * a1 + e0 * a2 + e1 * a3 + s0 * b1 + s1 * b2

    val s3 = a1 * e2 + e * a2 + e0 * a3 + s2 * b1 + s0 * b2

    val s4 = a1 * e3 + e2 * a2 + e * a3 + s3 * b1 + s2 * b2

    val s5 = a1 * e4 + e3 * a2 + e2 * a3 + s4 * b1 + s3 * b2

    val s6 = a1 * e5 + e4 * a2 + e3 * a3 + s5 * b1 + s4 * b2

    val s7 = a1 * e6 + e5 * a2 + e4 * a3 + s6 * b1 + s5 * b2

    val s8 = a1 * e7 + e6 * a2 + e5 * a3 + s7 * b1 + s6 * b2

    val s9 = a1 * e8 + e7 * a2 + e6 * a3 + s8 * b1 + s7 * b2

    val s10 = a1 * e9 + e8 * a2 + e7 * a3 + s9 * b1 + s8 * b2
    s10
  } ensuring(res => res <= 20.0 && noise(res, 1e-13))

}

/*
int main(int N) {
  double E, E0, E1, S0, S1, S;
  double A1, A2, A3;
  double B1, B2;
  int i;
  A1 = DBETWEEN(0.5, 0.8);
  A2 = DBETWEEN(-1.5,-1);
  A3 = DBETWEEN(0.8,1.3);
  B1 = DBETWEEN(1.39,1.41);
  B2 = DBETWEEN(-0.71,-0.69);
  E=DBETWEEN(0,1.0);
  E0=DBETWEEN(0,1.0);
  for (i=1;i<=N;i++) {
    E1 = E0;
    E0 = E;
    E = DBETWEEN(0,1.0);
    S1 = S0;
    S0 = S;
    S = A1 * E + E0 * A2 + E1 * A3 + S0 * B1 + S1 * B2 ;
    DPRINT(S);
  }
  DSENSITIVITY(S);
  return 0;
}
*/