/* Copyright 2013-2014 EPFL, Lausanne */

package leon
package real

import java.io.{PrintWriter, File}

import purescala.Trees._
import purescala.Definitions._
import purescala.TreeOps._
import purescala.TransformerWithPC

import real.Trees.{Noise, Roundoff, Actual, RealLiteral, RelError, WithIn}
import real.TreeOps._
import Sat._
import Valid._
import Approximations._
import FncHandling._
import ArithmApprox._
import PathHandling._
import Rational._


class Prover(ctx: LeonContext, options: RealOptions, prog: Program, fncs: Map[FunDef, Fnc]) {
  implicit val debugSection = utils.DebugSectionRealProver
  val reporter = ctx.reporter
  val solver = new RangeSolver(options.z3Timeout)

  // Returns the precision with which we can satisfy all constraints, or the last one tried,
  // as well as an indication whether verification was successfull.
  def check(vcs: Seq[VerificationCondition]): (Precision, Boolean) = {
    reporter.debug("VCs: " + vcs)
    val approximations = vcs.map(vc => (vc, Approximations(options, fncs, reporter, solver, vc))).toMap

    val precisions = options.precision

    def findPrecision(lowerBnd: Int, upperBnd: Int): (Precision, Boolean) = {
      if (lowerBnd > upperBnd) (precisions.last, false)
      else {
        val mid = lowerBnd + (upperBnd - lowerBnd) / 2// ceiling int division
        reporter.info("Checking precision: " + precisions(mid))
        if (checkVCsInPrecision(vcs, precisions(mid), approximations)) {
          if (lowerBnd == mid) (precisions(lowerBnd), true)
          else {
            findPrecision(lowerBnd, mid)
          }
        }
        else {
          if (lowerBnd == mid && upperBnd < precisions.length - 1) (precisions(upperBnd), true)
          else {
            findPrecision(mid + 1, upperBnd)
          }
        }
      }
    }

    reporter.debug("approximation kinds:")
    approximations.foreach(x => reporter.debug(x._1 + ": " + x._2.kinds))

    findPrecision(0, precisions.length - 1)
  }

  def checkVCsInPrecision(vcs: Seq[VerificationCondition], precision: Precision,
    approximations: Map[VerificationCondition, Approximations]): Boolean = {
    var postMap: Map[FunDef, Seq[Spec]] = vcs.map(vc => (vc.funDef -> Seq())).toMap

    //println("checking vcs: ")

    for (vc <- vcs if (options.specGen || vc.kind != VCKind.SpecGen)) {
      reporter.info("Verification condition  ==== %s (%s) ====".format(vc.fncId, vc.kind))
      reporter.debug("pre: " + vc.pre)
      reporter.debug("body: " + vc.body)
      reporter.debug("post: " + vc.post)

      val start = System.currentTimeMillis
      var spec: Seq[Spec] = Seq()

      val approx = approximations(vc)

      // TODO: can we re-use some of the approximation work across precision?
      approx.kinds.find(aKind => {
        reporter.info("approx: " + aKind)

        try {
          val currentApprox = approx.getApproximation(aKind, precision, postMap)
          spec = mergeSpecs(spec, currentApprox.spec)
          postMap += (vc.funDef -> currentApprox.spec)

          if (vc.kind == VCKind.SpecGen) true  // specGen, no need to check, only uses first approximation
          else
            checkValid(currentApprox, vc.variables, precision, vc.toString) match {
              case (VALID, str) =>
                reporter.info("==== VALID ====")
                vc.value += (precision -> VALID)
                writeToFile(vc, str)
                true
              case (INVALID, str) =>
                reporter.info("=== INVALID ===")
                vc.value += (precision -> INVALID)
                writeToFile(vc, str)
                true
              case (UNKNOWN, _) =>
                reporter.info("---- Unknown ----")
                false
              case (NothingToShow, _) =>
                vc.value += (precision -> NothingToShow)
                true
            }
        } catch {
          case PostconditionInliningFailedException(msg) =>
            reporter.info("failed to compute approximation: " + msg)
            false
          case RealArithmeticException(msg) =>
            reporter.warning("Failed to compute approximation: " + msg)
            false
          case FixedPointOverflowException(msg) =>
            reporter.warning("Insufficient bitwidth: " + msg)
            false
          case SqrtNotImplementedException(msg) =>
            reporter.warning(msg)
            false
          //case UnsoundBoundsException(msg) =>
          //  reporter.error(msg)
          //  return false

        }

      }) match {
        case None =>
        case _ =>
      }
      // TODO: there is a bug where not the correct spec is printed, see the InitialExample
      vc.spec += (precision -> spec)

      val end = System.currentTimeMillis
      vc.time = Some(end - start)
      reporter.info("generated spec: " + spec + " in " + (vc.time.get / 1000.0))
    }

    vcs.forall( vc => vc.kind == VCKind.SpecGen || vc.value(precision) != UNKNOWN )
  }

  /*
    @return (status, what we actually proved)
  */
  def checkValid(app: Approximation, variables: VariablePool, precision: Precision, name: String): (Valid, String) = {
    reporter.debug("checking for valid: " + app.constraints.mkString("\n"))
    var str = app.kind + "\n\n"

    val transformer = new LeonToZ3Transformer(variables, precision)
    var validCount = 0
    var invalidCount = 0

    for ((cnstr, index) <- app.constraints.zipWithIndex) {
      val realCnstr = addResults(cnstr.realComp, variables.resultVars)
      val finiteCnstr = addResultsF(cnstr.finiteComp, variables.fResultVars)

      str = str + "%d:\nP: %s\n\nreal: %s\n\nfin: %s\n\nQ: %s\n\n".format(index, cnstr.precondition,
        realCnstr, finiteCnstr, transformer.getZ3Expr(cnstr.postcondition)) 

      var sanityConstraint: Expr = And(cnstr.precondition, And(realCnstr, finiteCnstr))  
      if (options.removeRedundant) {
        val args = removeRedundantConstraints(sanityConstraint, cnstr.postcondition)
        sanityConstraint = And(args.toSeq)
      }
      if (options.simplifyCnstr) {
        sanityConstraint = simplifyConstraint( sanityConstraint )
      }
      if (options.massageArithmetic) {
        sanityConstraint = massageArithmetic (sanityConstraint)
      }

      val toCheck = And(sanityConstraint, negate(cnstr.postcondition))

      val z3constraint = transformer.getZ3Expr(toCheck)
      reporter.debug("z3constraint ("+index+"): " + z3constraint)

      val sanityExpr = transformer.getZ3Expr(sanityConstraint)

      if (reporter.errorCount == 0 && sanityCheck(sanityExpr, name + "-" +app.kind.toString)) {
        solver.checkSat(z3constraint) match {
          case (UNSAT, _) =>
            reporter.info(s"Constraint with $index is valid.")
            validCount += 1
          case (SAT, model) =>
            if (app.kind.allowsRealModel) {
              // Idea: check if we get a counterexample for the real part only, that is then a possible counterexample, (depends on the approximation)
              
              val realOnlyPost = removeErrorsAndActual(cnstr.postcondition)

              if (realOnlyPost == True) { // i.e. if the constraint is trivially true
                reporter.info("Nothing to prove for real-only part.")
              } else {
                var realOnlyConstraint = And(removeErrorsAndActual(And(cnstr.precondition, realCnstr)), negate(realOnlyPost))
                
                if (options.massageArithmetic) {
                  realOnlyConstraint = massageArithmetic(realOnlyConstraint)
                }
                solver.checkSat(transformer.getZ3Expr(realOnlyConstraint)) match {
                  case (SAT, model) =>
                    // TODO: pretty-print the models
                    reporter.info("counterexample: " + model)
                    invalidCount += 1
                  case (UNSAT, _) =>
                  case _ =>
                }
              }
            } else {
              reporter.info(s"Constraint with $index is unknown.")
            }


          case _ =>;
        }
      }
    }
    if (app.constraints.isEmpty) (NothingToShow, "")
    else if ( (validCount + invalidCount) < app.constraints.length) (UNKNOWN, "")
    else if (invalidCount > 0) (INVALID, str)
    else (VALID, str)
  }

  // if true, we're sane
  // TODO: make a method in the solver and then we don't need to duplicate
  private def sanityCheck(pre: Expr, name: String = "", body: Expr = BooleanLiteral(true)): Boolean = {
    val sanityCondition = And(pre, body)
    solver.checkSat(sanityCondition) match {
      case (SAT, model) => true
      case (UNSAT, model) =>
        reporter.warning("Not sane! " + sanityCondition)
        //writeToFile( SMTLib.printSMTLib2(sanityCondition), name="not-sane-"+name)
        false
      case _ =>
        reporter.info("Sanity check failed! ")// + sanityCondition)
        false
    }
  }


  private def writeToFile(vc: VerificationCondition, str: String) = {
    val writer = new PrintWriter(new File("vcs/" + vc.toString + ".txt"))
    writer.write("VC: " + vc.longStringWithBreaks + "\n\n\n" + "proved by " + str)
    writer.close()
  }

  private def writeToFile(assertions: Seq[String], name: String) = {
    val writer = new PrintWriter(new File("smt/" + name + ".smt2"))
    assertions.foreach{ a =>
      writer.write(a+ "\n")
    }
    writer.close()
  }
}