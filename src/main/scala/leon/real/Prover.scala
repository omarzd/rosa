/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package real

import java.io.{PrintWriter, File}

import purescala.Trees._
import purescala.Definitions._
import purescala.TreeOps._
import purescala.TransformerWithPC

import real.Trees.{Noise, Roundoff, Actual, RealLiteral, RelError, WithIn, FncValue}
import real.TreeOps._
import Sat._
import Valid._
import Approximations._
import FncHandling._
import ArithmApprox._
import PathHandling._
import Rational._
import VariableShop._


class Prover(ctx: LeonContext, options: RealOptions, prog: Program, fncs: Map[FunDef, Fnc]) {
  implicit val debugSection = utils.DebugSectionRealProver
  val reporter = ctx.reporter
  val rangeSolver = new RangeSolver(options.z3Timeout)
  val solver = new NonIncrementalRangeSolver(options.z3Timeout)
  //val solver = new RangeSolver(options.z3Timeout)

  // Returns the precision with which we can satisfy all constraints, or the last one tried,
  // as well as an indication whether verification was successfull.
  def check(vcs: Seq[VerificationCondition]): (Precision, Boolean) = {
    reporter.debug("VCs: " + vcs)
    val approximations = vcs.map(vc => (vc, Approximations(options, fncs, reporter, rangeSolver, vc))).toMap

    val precisions = options.precision

    def findPrecision(lowerBnd: Int, upperBnd: Int): (Precision, Boolean) = {
      if (lowerBnd > upperBnd) (precisions.last, false)
      else {
        val mid = lowerBnd + (upperBnd - lowerBnd) / 2// ceiling int division
        if (!options.silent) reporter.info("Checking precision: " + precisions(mid))
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

    for (vc <- vcs ) {
      if (!options.silent) reporter.info("Verification condition  ==== %s (%s) ====".format(vc.fncId, vc.kind))
      else reporter.info(vc.fncId)
      reporter.debug("pre: " + vc.pre)
      reporter.debug("body: " + vc.body)
      reporter.debug("post: " + vc.post)

      val start = System.currentTimeMillis
      var spec: Seq[Spec] = Seq()

      val approx = approximations(vc)

      // TODO: can we re-use some of the approximation work across precision?
      approx.kinds.find(aKind => {
        val internalStart = System.currentTimeMillis
        RealRange.solverTime = 0l
        RangeSolver.solverTime = 0l
        RangeSolver.waitingTime = 0l
        RangeSolver.timeoutTime = 0l
        if (!options.silent) reporter.info("approx: " + aKind)

        try {
          rangeSolver.clearCounts
          val currentApprox = approx.getApproximation(aKind, precision, postMap)
          if (!options.silent) reporter.info(rangeSolver.getCounts)
          spec = Spec.mergeSpecs(spec, currentApprox.spec)
          postMap += (vc.funDef -> currentApprox.spec)

          //reporter.info("internal time: " + (System.currentTimeMillis - start))
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
            if (!options.silent) reporter.info("failed to compute approximation: " + msg)
            false
          case RealArithmeticException(msg) =>
            if (!options.silent) reporter.warning("Failed to compute approximation: " + msg)
            false
          case FixedPointOverflowException(msg) =>
            reporter.warning("Insufficient bitwidth: " + msg)
            false
          case SqrtNotImplementedException(msg) =>
            reporter.warning(msg)
            false
          case i: java.lang.ArithmeticException =>
            reporter.warning("Something went wrong, probably insufficient accuracy during the analysis:\n")
            false
          case DivisionByZeroException(_) =>
            reporter.warning("Division by zero. Probably insufficient accuracy.")
            false
          //case UnsoundBoundsException(msg) =>
          //  reporter.error(msg)
          //  return false

        }

      }) match {
        case None =>
        case _ =>
      }
      vc.spec += (precision -> spec)

      val end = System.currentTimeMillis
      /*reporter.info("XNum solver time: " + RealRange.solverTime)
      reporter.info("RangeSolver time: " + RangeSolver.solverTime)
      reporter.info("RangeSolver waiting: " + RangeSolver.waitingTime)
      reporter.info("RangeSolver timeout time: " + RangeSolver.timeoutTime)
      reporter.info("Total time: " + (end - start))*/
      vc.time = Some(end - start)
      spec.foreach { sp => 
        reporter.info(sp)
      }
      if (!options.silent) {
        reporter.info("in " + (vc.time.get / 1000.0))
      }
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
      reporter.debug("\nsanityConstraint before preprocessing:")
      reporter.debug(sanityConstraint)

      sanityConstraint = preprocessFunctions(sanityConstraint)
      
      if (options.removeRedundant) {
        var args = removeRedundantConstraints(sanityConstraint, transformer.getZ3Expr(cnstr.postcondition))
        
        if (!belongsToActual(cnstr.postcondition))
          args = args.filter(x => !belongsToActual(x))

        sanityConstraint = And(args.toSeq)
      }
      
      if (options.simplifyCnstr) {
        sanityConstraint = simplifyConstraint( sanityConstraint )
      }
      if (options.massageArithmetic) {
        sanityConstraint = massageArithmetic (sanityConstraint)
      }
      //println("\nafter massage arithm.: " + sanityConstraint)

      val toCheck = And(sanityConstraint, negate(transformer.getZ3Expr(cnstr.postcondition)))

      val z3constraint = transformer.getZ3Expr(toCheck)
      reporter.debug("z3constraint ("+index+"): " + z3constraint)

      val sanityExpr = transformer.getZ3Expr(sanityConstraint)
      
      if (reporter.errorCount == 0 && sanityCheck(sanityExpr, name + "-" +app.kind.toString)) {
        solver.checkSat(z3constraint) match {
          case (UNSAT, _) =>
            if (!options.silent) reporter.info(s"Constraint $index is valid.")
            validCount += 1
          case (SAT, model) =>
            // TODO: this needs to be re-checked, seems to have a bug with pathError/Fluctuat/simpleInterpolator
            if (app.kind.allowsRealModel) {
              // Idea: check if we get a counterexample for the real part only, that is then a possible counterexample, (depends on the approximation)
              //println("checking for counterexample")
              val realOnlyPost = removeErrorsAndActual(cnstr.postcondition)

              if (realOnlyPost == True) { // i.e. if the constraint is trivially true
                if (!options.silent) reporter.info("Nothing to prove for real-only part.")
              } else {
                var realOnlyConstraint = And(removeErrorsAndActual(And(cnstr.precondition, realCnstr)), negate(realOnlyPost))
                //println("realOnlyConstraint: " + realOnlyConstraint)         
                if (options.massageArithmetic) {
                  realOnlyConstraint = massageArithmetic(realOnlyConstraint)
                }
                // TODO: this seems to have a bug in Fluctuat/simpleInterpolator
                //println("after massage: " + realOnlyConstraint)
                solver.checkSat(transformer.getZ3Expr(realOnlyConstraint)) match {
                  case (SAT, model) =>
                    // TODO: pretty-print the models
                    if (!options.silent) reporter.info(s"Constraint with $index, counterexample: " + model)
                    invalidCount += 1
                  case (UNSAT, _) =>
                  case _ =>
                }
              }
            } else {
              if (!options.silent) reporter.info(s"Constraint $index is unknown.")
            }
            if (!options.silent) reporter.info(s"Constraint with $index is unknown.")

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

  private def preprocessFunctions(e: Expr): Expr = {
    var extra: Expr = True
    
    val tmp = preMap { expr => expr match {
      case FncValue(specs, specExpr, _, _, _) =>
        val fresh = getNewXFloatVar
        // TODO: tuples: fresh will have to be a tuple?
        extra = And(extra, replace(Map(Variable(specs(0).id) -> fresh), specExpr))
        Some(fresh)
      case _ => None
      }
    }(e)

    And(tmp, extra)
  }
}
