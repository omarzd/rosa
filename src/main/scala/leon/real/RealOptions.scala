/* Copyright 2013 EPFL, Lausanne */

package leon
package real

//import Precision._

case class RealOptions(
  simulation: Boolean           = false,        // determine ranges and errors with simulation
  z3Timeout: Long               = 1000l,        // timeout for Z3
  precision: List[Precision]    = List(Float64),// which precisions to try, in the given order
  z3Only: Boolean               = false,        // also try the un-approximated constraint on Z3
  solverMaxIter: Int            = solverMaxIterMedium,
  solverPrecision: Rational     = solverPrecisionMedium,
  specGen: Boolean              = false,        // generate specs for functions without postconditions?
  loopUnrolling: Boolean        = true,         // whether to (also) unroll loops up to max given by loopBound annotation
  simplifyCnstr: Boolean        = true,        // simplify constraint before passing to Z3
  massageArithmetic: Boolean    = true,         // whether to massage arithmetic before passing to Z3
  removeRedundant: Boolean      = true,         // remove redundant constraints before passing to Z3
  lipschitz: Boolean            = false,        // compute Lipschitz constants
  lipschitzPathError: Boolean   = true          // compute path error with new lipschitz-based procedure

) {
  override def toString: String = 
    "simulation: %b, z3Timeout: %d, precision: %s, z3Only: %b, solverMaxIter: %d, solverPrecision: %s,".format(
      simulation, z3Timeout, precision.toString, z3Only, solverMaxIter, solverPrecision.toString) +
    " specGen: %b, loopUnrolling: %b, simplifyCnstr: %b, massageArithmetic: %b, ".format(
       specGen, loopUnrolling, simplifyCnstr, massageArithmetic) +
    "removeRedundant: %s, lipschitz: %s, lipschitzPathError: %s".format(removeRedundant, lipschitz, lipschitzPathError)
}
