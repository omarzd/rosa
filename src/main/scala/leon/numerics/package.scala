package leon

import ceres.common.{Rational, DirectedRounding}

package object numerics {

  case class UnsupportedFragmentException(msg: String) extends Exception(msg)

  object Sat extends Enumeration {
    type Sat = Value
    // caps so it does not clash with the type name
    val SAT = Value("SAT")
    val UNSAT = Value("UNSAT")
    val Unknown = Value("UNKNOWN")
  }


  /*def scaleToIntsUp(r: Rational): Rational = {
    if (r.n.abs > Int.MaxValue || r.d > Int.MaxValue) {
      val value = DirectedRounding.divUp(r.n.toDouble, r.d.toDouble) 

      val res = Rational(value)
      assert(res.toDouble >= r.toDouble, "res (" + res.toDouble + ") is smaller than before (" + r.toDouble)
      println("before: " + r + "     after: " + res)
      res
    } else {
      r
    }
  }

  // TODO: fix this, only do something if it's necessary
  def scaleToIntsDown(r: Rational): Rational = {
    if (r.n.abs > Int.MaxValue || r.d > Int.MaxValue) {
      val value = DirectedRounding.divDown(r.n.toDouble, r.d.toDouble) 

      val res = Rational(value)
      assert(res.toDouble <= r.toDouble, "res (" + res.toDouble + ") is larger than before (" + r.toDouble)
      println("before: " + r + "     after: " + res)
      println("before: " + r.toFractionString + "     after: " + res.toFractionString)

      println(r.n < Int.MaxValue)
      println(r.d < Int.MaxValue)
      res
    } else {
      r
    }
  }*/


}
