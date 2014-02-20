
import leon.Real
import Real._

  /**
   * Source: Eric Jenn, Thales

Title :PBD precision
Content :The algorithm precision is defined regarding the WGS84 model.

The precision is expected to be respected only if the hypothesis are met.
HYPOTHESIS : 
  P1, P2 are the extremities position of the segment. 
  P1 is the Place (input)
  P2 is the Resulting_Position (Output)
The distance P1P2 is between 0.03Nm and 2000 Nm.
"_reference" is computed using a non-simplified algorithm based on the WGS84 model

EXPECTED PRECISION
DISTANCE
IF (0<Distance_reference<125Nm or Distance_reference>150Nm) THEN
  the error on the distance shall be less than max(0.0004*Distance_reference;0.1Nm)
ELSE 
  the error shall be less than 0.05Nm 

BEARING
The error shall be less than 0.001° for a distance greater than 0,05Nm 
(half of HMI minimum distance and 2*distance_mini_to_distinguish)
   */
object BasicGeo {
/* Comments: 
  - upper bound on distance?
  - how to handle constants like Pi?
*/


  /**
   * Compute the Orthodromic Place Bearing Distance (PBD) Point
   *
   * @param latitude  in degrees
   * @param longitude in degrees
   * @param true_bearing in degrees (positive angle / clockwise / 0° to North)
   * @param distance  in nautical miles
   * @return [ lat(deg) , long(deg) ]
   */
  def computePBD(latitude: Real, longitude: Real, trueBearing: Real, distance: Real): (Real, Real) = {
    require(-90 <= latitude && latitude <= 90 && -180 <= longitude && longitude <= 180 &&
      0 <= trueBearing && trueBearing <= 360 && 0 <= distance)

    /** Earth excentricity correction */               
    val earthModelFlat: Real = 0.003367

    val a0: Real = 3444.053984
    val f: Real = earthModelFlat
    val Pi: Real = Math.PI

    /*double B1, L1, S, A12, B2;
    double BETA1, RO, E2, M1, H, ERE, A1, COS_BETA0, V;
    double L_PRIME_2, L_PRIME_C, LC;
    double SIN_BETA1, COS_BETA1, SIN_R, COS_R, SIN_2R;
    double COS_A12, SIN_A12, SIN_RO, COS_RO;
    double out[] = new double[2];
    */
    //val B1 = latitude
    //L1 = longitude;
    val s = distance

    // note that for this algorithm the angles must have other sign
    // convention.
    val a12 = -trueBearing

    val cosA12 = cos(toRadians(a12))
    val sinA12 = sin(toRadians(a12))

    val e2 = 1.0 / ((1.0 - f) * (1.0 - f)) - 1.0

    val beta1 = atan((1.0 - f) * tan(toRadians(latitude))) // BETA1 in rad
    val sinBeta1 = sin(beta1)
    val cosBeta1 = cos(beta1)

    val cosBeta0 = cosBeta1 * sinA12
    val h = 1.0 + ((e2 * sinBeta1 * sinBeta1) / 2.0)
    val m1 = h * (1.0 - cosBeta0 * cosBeta0)

    val ere = toDegrees(s) / ((1.0 - f) * a0)
    val sinR = sin(toRadians(ere))
    val cosR = cos(toRadians(ere))
    val sin2R = sin(2.0 * toRadians(ere))
    //Math.cos(2.0 * Math.toRadians(ere));  (assigned to no variable)

    val a1 = h * ((sinBeta1 * sinBeta1 * cosR) + (cosBeta1 * cosA12 * sinBeta1 * sinR))

    val ro = ere - (90.0 * A1 * e2 * sinR / Pi) - 
              (m1 * e2 * (2.0 * ere - (180.0 * sin2R / Pi)) / 8.0) + 
              (225.0 * a1 * a1 * e2 * e2 * sin2R / (4.0 * Pi)) + 
              (m1 * m1 * e2 * e2 * (22.0 * ere - 2340.0 * sin2R / Pi - 16.0 * ere * cosR * cosR + 1800.0 * cosR * cosR * sin2R / Pi) / 128.0) + 
              a1 * m1 * e2 * e2 * (1080.0 * sinR / Pi + 4.0 * ere * cosR - 900.0 * cosR * sin2R / Pi) / 16.0

    val cosRo = cos(toRadians(ro))
    val sinRo = sin(toRadians(ro))
    val b2 = toDegrees(
              atan((sinBeta1 * cosRo + cosBeta1 * cosA12 * sinRO) / 
                ((1.0 - f) * sqrt(cosBeta0 * cosBeta0 + (cosRo * cosBeta1 * cosA12 - sinBeta1 * sinRo)*
                   (cosRo * cosBeta1 * cosA12 - sinBeta1 * sinRo)))))

    val lc = toDegrees(atan2(sinRo * sinA12, cosBeta1 * cosRo - sinBeta1 * sinRo * cosA12))
    val lPrimeC = lc

    val v = 270.0 * a1 * f * f * sinR / Pi - f * ere + 3.0 * m1 * f * f / 4.0 * (ere - 90.0 * sin2R / Pi)
    val lPrime2 = longitude - v * cosBeta0 - lPrimeC

    // Result
    val out0 = b2 // Latitude in degrees
    val out1 = li180(lPrime2) // Longitude in degrees
    return (out0, out1)
  }
  
  /**
   * Returns an angle (deg) between [-180 and +180]
   * 
   * @param angle
   *            in degrees
   * @return angle between [-180 and +180] in degrees
   ==> Comment: if we know the maximum range of the input we may not need a general loop
   */ 
  public static double li180(double angle) {
    while (angle < -180)
      angle += 360;
    while (angle > 180)
      angle -= 360;
    return angle;
  }

}