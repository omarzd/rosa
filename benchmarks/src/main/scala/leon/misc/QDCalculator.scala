package leon
package misc

import ceres.common.{DoubleDouble, QuadDouble => QD}

object QDCalculator extends App {

  val e = QD(118219490218475521.0) / QD(4728779608739021.0)

  println(e)

  val res = QD(628927687962289809.0) / QD(18915118434956084.0)

  println(res)
}