/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import Precision._

case class RealOptions(
  simulation: Boolean           = false,        // determine ranges and errors with simulation
  z3Timeout: Long               = 1000l,        // timeout for Z3
  precision: List[Precision]    = List(Float64),// which precisions to try, in the given order
  z3Only: Boolean               = false,        // also try the un-approximated constraint on Z3
  solverMaxIter: Int            = solverMaxIterMedium,
  solverPrecision: Rational     = solverPrecisionMedium,
  specGen: Boolean              = false,        // generate specs for functions without postconditions?
  pathError: Boolean            = false         // checking path error, experimental feature :-)
  
)