package leon
package experiments

import ceres.common.{DoubleDouble, QuadDouble => QD}

object SineExperiments {


  def sine = {

    def sD(x: Double): Double = x - (x*x*x)/6.0 + (x*x*x*x*x)/120.0 -
      (x*x*x*x*x*x*x)/5040.0

    def sQD(x: QD): QD = x - (x*x*x)/QD(6.0) + (x*x*x*x*x)/QD(120.0) -
      (x*x*x*x*x*x*x)/QD(5040.0)

    println(sD(1.5707))
    println(sQD(1.5707))

    println((sD(1.5707) - sQD(1.5707)))
  }

}