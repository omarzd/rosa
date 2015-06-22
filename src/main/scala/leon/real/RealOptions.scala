/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package real

case class RealOptions(
  simulation: Boolean           = false,        // determine ranges and errors with simulation
  z3Timeout: Long               = 1000l,        // timeout for Z3
  precision: List[Precision]    = List(FPPrecision(8), FPPrecision(16), FPPrecision(32), Float32, Float64, DoubleDouble, QuadDouble),// which precisions to try, in the given order
  z3Only: Boolean               = false,        // also try the un-approximated constraint on Z3

  //specGen: Boolean              = false,        // generate specs for functions without postconditions?
  loopUnrolling: Boolean        = false,         // whether to (also) unroll loops up to max given by loopBound annotation
  simplifyCnstr: Boolean        = true,         // simplify constraint before passing to Z3
  massageArithmetic: Boolean    = true,         // whether to massage arithmetic before passing to Z3
  removeRedundant: Boolean      = true,         // remove redundant constraints before passing to Z3
  lipschitz: Boolean            = true,        // compute Lipschitz constants
  lipschitzPathError: Boolean   = true,         // compute path error with new lipschitz-based procedure
  silent: Boolean               = true
) {
  override def toString: String =
    "simulation: %b, z3Timeout: %d, precision: %s, z3Only: %b, ".format(
      simulation, z3Timeout, precision.toString, z3Only) +
    "loopUnrolling: %b, simplifyCnstr: %b, massageArithmetic: %b, ".format(
      loopUnrolling, simplifyCnstr, massageArithmetic) +
    "removeRedundant: %s, lipschitz: %s, lipschitzPathError: %s".format(removeRedundant, lipschitz, lipschitzPathError)
}
