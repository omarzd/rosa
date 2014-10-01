import leon.real._
import RealOps._

object Fluctuat {

  //Robustness Analysis of Finite Precision Implementations, arxiv extended version,
  // E. Goubault, S. Putot

  /*
  "The analysis finds that the interpolated res is within [-2.25e-5,33.25],
   with an error within [-3.55e-5,2.4e-5], that is of the order of magnitude
   of the input error despite unstable tests."

   // in Fluctuat this is in single precision
  */
  def simpleInterpolator(e: Real): Real = {
    require(0.0 <= e && e <= 100.0 && e +/- 0.00001)

    
    val r1: Real = 0.0
    val const: Real = 2.25  // else this would be pre-evaluated by the parser
    val r2: Real = 5 * const
    val const2: Real = 1.1
    val r3: Real = r2 + 20 * const2  //same here

    if (e < 5)
      e * 2.25 + r1
    else if (e < 25)
      (e - 5) * 1.1 + r2
    else
      r3
  } ensuring (res => -2.25e-5 <= res && res <= 33.26 && res +/- 3.5e-5)

  /*
    "Result is in the real number semantics within [1,1.4531]
    with a global error within [-0.03941,0.03895],
    the discontinuity at the test accounting for most of it,
     i.e. an error within [-0.03898,0.03898]"
  */
  def squareRoot(i: Real): Real = {
    // the error should be [0, 0.001]
    require(1.0 <= i && i <= 2.0 && i +/- 0.001)

    val sqrt2: Real = 1.414213538169860839843750

    if (i >= 2)
      sqrt2 * (1.0 + (i/2 - 1) * (0.5 - 0.125 * ( i/2 - 1)))
    else
      1 + (i - 1) * (0.5 + (i-1) * (-0.125 + (i - 1) * 0.0625))
  } ensuring (res => 1 <= res && res <= 1.4531 && res +/- 0.03941)

}

/*
Original:

Interpolator:

float R1[3], E, res;
R1[0] = 0; R1[1]= 5 * 2.25; R1[2] = R1[1] + 20 * 1.1;
E = FREAL_WITH_ERROR(0.0,100.0, -0.00001, 0.00001);
if (E < 5)
res = E*2.25 + R1[0];
else if (E < 25)
res = (E-5)*1.1 + R1[1] ;
else
res = R1[2];
return res;


Square root:

double sqr t 2 = 1.414213538169860839843750;
double S, I; I = DREAL_WITH_ERROR(1, 2, 0, 0.001);
if ( I>=2)
S = sqrt2 *(1+(I/2-1) * (.5 -0.125*(I/2-1)));
else
S = 1+(I-1)*( .5+(I-1)*( - .125+( I - 1 ) * .0625));

*/