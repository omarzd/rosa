
import leon.real._
import RealOps._

/* From:
  Numerical Methods with Worked Examples, C. Woodford and C. Phillips, 2012
*/
object TurbineTuple {

  def turbine(v: Real, w: Real, r: Real): (Real, Real, Real) = {
    require(-4.5 <= v && v <= -0.3 && 0.4 <= w && w <= 0.9 && 3.8 <= r && r <= 7.8)//&&
      //v +/- 1e-7 && w +/- 1e-12 && r +/- 1e-8)

    val v1 = 3 + 2/(r*r) - 0.125*(3-2*v)*(w*w*r*r)/(1-v) - 4.5
    val v2 = 6*v - 0.5 * v * (w*w*r*r) / (1-v) - 2.5
    val v3 = 3 - 2/(r*r) - 0.125 * (1+2*v) * (w*w*r*r) / (1-v) - 0.5

    (v1, v2, v3)
  } ensuring (_ match {
    case (v1, v2, v3) =>
      -18.525727 < v1 && v1 < -1.991604 && v1 +/- 1.24162e-13 &&
      -28.55484 < v2 && v2 < 3.822207 && v2 +/- 1.757041e-13 &&
      0.571726 < v3 && v3 < 11.4272 && v3 +/- 8.49926e-14
  })

  def turbineTest(v: Real, w: Real, r: Real): (Real, Real, Real) = {
    require(-4.5 <= v && v <= -0.3 && 0.4 <= w && w <= 0.9 && 3.8 <= r && r <= 7.8)//&&
      //v +/- 1e-7 && w +/- 1e-12 && r +/- 1e-8)

    val (v1, v2, v3) = turbine(v, w, r)
    (v1, v2, v3)
  } ensuring (_ match {
    case (v1, v2, v3) =>
      -18.525727 < v1 && v1 < -1.991604 && v1 +/- 1.24162e-13 &&
      -28.55484 < v2 && v2 < 3.822207 && v2 +/- 1.757041e-13 &&
      0.571726 < v3 && v3 < 11.4272 && v3 +/- 8.49926e-14
  })

}