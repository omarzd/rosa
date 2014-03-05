/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import purescala.Common._
import purescala.Trees._
import purescala.Definitions._
import purescala.TreeOps._

import real.Trees.{Noise, Roundoff, Actual, UpdateFunction, Iteration}
import real.TreeOps._
import Rational._
import Calculus._

class Approximations(options: RealOptions, fncs: Map[FunDef, Fnc],
  reporter: Reporter, solver: RangeSolver) {
  import Approximations._
  import FncHandling._
  import ArithmApprox._
  import PathHandling._

  implicit val debugSection = utils.DebugSectionReals

  // Note: only supports function calls in fnc bodies, not in pre and post
  def getApproximation(vc: VerificationCondition, kind: ApproxKind, precision: Precision,
    postMap: Map[FunDef, Seq[Spec]]): Approximation = {
    val leonToZ3 = new LeonToZ3Transformer(vc.variables, precision)

    def isFeasible(pre: Expr): Boolean = {
      import Sat._
      solver.checkSat(leonToZ3.getZ3Expr(pre)) match {
        case (SAT, model) => true
        case (UNSAT, model) => false
        case _ =>
          reporter.error("Sanity check failed! ")// + sanityCondition)
          false
      }
    }

    /*
      Computing sigma (roundoff error, strating with exact inputs) and
      K, Lipschitz constant, of a potentially multivariate function.
      @param ids function variables 
    */
    def getSigmaK(precondition: Expr, expr: Expr, exprf: Expr, ids: Seq[Identifier]): (Rational, Rational) = {
      val transformer = new Approximator(reporter, solver, precision, vc.pre, vc.variables, false, true)
      val sigma = transformer.computeError(exprf)

      reporter.debug("\u03C3: " + sigma)
      val k = maxAbs(ids.flatMap { x =>
        val exprPrime = d(expr, x)
        val rangeDerivative = solver.getRange(precondition, exprPrime, vc.variables,
                    solverMaxIterMedium, solverPrecisionMedium) 
        reporter.debug("Lipschitz constants wrt " + x + ": " + rangeDerivative.xlo +
                        ", " + rangeDerivative.xhi)
        Seq(rangeDerivative.xlo, rangeDerivative  .xhi)
        })
      reporter.debug("k: " + k)
      (sigma, k)
    }

    /* --------------  Functions -------------- */
    val (pre, bodyFnc, post) = kind.fncHandling match {
      case Uninterpreted => (vc.pre, vc.body, vc.post)
      case Postcondition => (vc.pre, inlinePostcondition(vc.body, precision, postMap), vc.post)
      case Inlining => (vc.pre, inlineFunctions(vc.body, fncs), vc.post)
    }
    if (kind.fncHandling != Uninterpreted)
      reporter.debug("after FNC handling:\npre: %s\nbody: %s\npost: %s".format(pre,bodyFnc,post))

    /* -------------- If-then-else -------------- */
    val paths: Set[Path] = kind.pathHandling match {
      case Pathwise => getPaths(bodyFnc).map {
        case (cond, expr) => Path(cond, expr, idealToActual(expr, vc.variables))
      }
      case Merging =>  Set(Path(True, bodyFnc, idealToActual(bodyFnc, vc.variables)))
    }
    reporter.debug("after PATH handling:\nbody: %s".format(paths.mkString("\n")))



    if (vc.isLoop) {
      reporter.debug("vc is a loop")
      var constraints = Seq[Constraint]()

      bodyFnc match {
        case Iteration(ids, body, updateFncs) =>
          val inlinedUpdateFns = inlineBody(body, updateFncs.asInstanceOf[Seq[UpdateFunction]])
          reporter.debug("inlined fncs: " + inlinedUpdateFns)

          val precondition = removeErrors(vc.pre)//removeErrors(vc.pre)

          // List[(maxError, max Lipschitz constant, max loop error)]
          val errors: Seq[(Rational, Rational, Option[Rational])] = inlinedUpdateFns.map({
            case UpdateFunction(v, expr) =>
              reporter.debug("")
              reporter.debug("real update fnc for " + v + ": " + expr)
              // TODO: this has already been done before (with path handling)
              val exprFinite = idealToActual(expr, vc.variables)
              reporter.debug("finite expr: " + exprFinite)

              val (sigma, k) = getSigmaK(precondition, expr, exprFinite, ids)
              
              vc.funDef.loopBound match {
                case Some(n) =>
                  val initErrors = getInitialErrors(vc.variables, precision)
                  println("initErrors" + initErrors)
                  val totalError = errorFromNIterations(n, maxAbs(initErrors.values.toSeq), sigma, k)
                  reporter.info(s"($sigma, $k), error after " + n + "iterations: " + totalError)
                     
                  (sigma, k, Some(totalError))
                case _ => 
                  reporter.info(s"($sigma, $k)")  
                  (sigma, k, None)
              }
          })
        case _ => reporter.error("cannot handle anything but a simple loop for now...")
      }

      Approximation(kind, constraints, emptySpecTuple)
    } else {
      kind.arithmApprox match {
        case Z3Only =>
          var constraints = Seq[Constraint]()
          for (path <- paths) {
            constraints :+= Constraint(And(pre, path.condition), path.bodyReal, path.bodyFinite, post)
          }
          Approximation(kind, constraints, Seq())

        case JustFloat =>
          var constraints = Seq[Constraint]()
          var specsPerPath = Seq[SpecTuple]()
          var spec: SpecTuple = Seq() // seq since we can have tuples

          for ( path <- paths if (isFeasible(And(pre, path.condition))) ) {

            // TODO: only works on straight-line code
            val ids = vc.variables.inputs.keys.map(k => k.asInstanceOf[Variable].id).toSeq
            reporter.debug("ids: " + ids)
            // TODO: removing errors here is not sound, we need total ranges, including errors
            val (sigma, k) = getSigmaK(removeErrors(vc.pre), path.bodyReal, path.bodyFinite, ids)
            val initErrors = getInitialErrors(vc.variables, precision)
            reporter.debug("initial errors: " + initErrors)
            val totalError = errorFromNIterations(1, maxAbs(initErrors.values.toSeq), sigma, k)
            reporter.info(s"($sigma, $k), total error: " + totalError)

            //solver.clearCounts
            val transformer = new Approximator(reporter, solver, precision, And(pre, path.condition),
                                                vc.variables, options.pathError)
            val (bodyFiniteApprox, nextSpecs) =
              transformer.transformWithSpec(path.bodyFinite, vc.kind == VCKind.Precondition)
            //println("solver counts: " + solver.getCounts)
            spec = mergeSpecs(spec, nextSpecs)
            //if(!nextSpec.isEmpty)
            reporter.info("traditionally computed error: " + nextSpecs)
            specsPerPath :+= nextSpecs//.get// else specsPerPath :+= DummySpec
            reporter.debug("body after approx: " + bodyFiniteApprox)
            constraints :+= Constraint(And(pre, path.condition), path.bodyReal, bodyFiniteApprox, post)
          }
          val approx = Approximation(kind, constraints, spec)
          vc.approximations += (precision -> (vc.approximations(precision) :+ approx))
          approx.specsPerPath = specsPerPath
          approx

        case FloatNRange => // assumes that a JustFloat approximation has already been computed
          val justFloatApprox = vc.approximations(precision).find(a =>
            a.kind.fncHandling == kind.fncHandling && a.kind.pathHandling == kind.pathHandling && a.kind.arithmApprox == JustFloat
            )

          justFloatApprox match {
            case Some(approx) =>
              val newConstraints =
                for (
                  (cnstr, specs) <- approx.constraints.zip(approx.specsPerPath)
                ) yield
                  Constraint(cnstr.precondition, And(specs.map(specToRealExpr(_))), cnstr.finiteComp, cnstr.postcondition)
              Approximation(kind, newConstraints, approx.spec)
            case None =>
              throw new RealArithmeticException("Cannot compute Float'n'Range approximation because JustFloat approximation is missing.")
              null
          }
      }
    }
  }


  

  private def inlineBody(body: Expr, updateFncs: Seq[UpdateFunction]): Seq[UpdateFunction] = {
    var valMap: Map[Expr, Expr] = Map.empty
    preTraversal { expr => expr match {
        case Equals(v @ Variable(id), rhs) =>
          valMap = valMap + (v -> replace(valMap,rhs))
        case _ => ;
      }
    }(body)
    updateFncs.map( uf => UpdateFunction(uf.lhs, replace(valMap, uf.rhs)))
  }

  private def maxAbs(nums: Seq[Rational]): Rational = nums match {
    case Seq(n) => abs(n)
    case _ => max(abs(nums.head), maxAbs(nums.tail))
  }


  def getInitialErrors(variables: VariablePool, precision: Precision): Map[Identifier, Rational] = {
    var map = Map[Identifier, Rational]()
    val machineEps = getUnitRoundoff(precision)
    variables.inputs.map({
      case (Variable(id), Record(_,_, Some(lo),Some(up), Some(absError), _)) =>
        map += (id -> absError)
      case (Variable(id), Record(_,_, Some(lo),Some(up), _, _)) =>
        map += (id -> machineEps * max(abs(lo), abs(up)))
    })
    map
  }

    
}

object Approximations {

  /*
    @param n number of iterations
    @param lambda initial error
    @param sigma error of one loop iteration
    @param K Lipschitz constant
  */
  def errorFromNIterations(n: Int, lambda: Rational, sigma: Rational, k: Rational): Rational = {
    var kn = k
    for (i <- 1 until n) { kn *= k }

    kn * lambda + sigma * ((one - kn)/(one - k))
  }

  // to avoid confusion with nested sequences
  type SpecTuple = Seq[Spec]
  val emptySpecTuple: SpecTuple = Seq.empty

  def mergeSpecs(currentSpec: SpecTuple, newSpecs: SpecTuple): SpecTuple = (currentSpec, newSpecs) match {
    case (Seq(), specs) => specs

    case (current, Seq()) => current

    case _ =>
      currentSpec.zip(newSpecs).map({
        case (s1, s2) =>
          val lowerBnd = min(s1.bounds.xlo, s2.bounds.xlo)
          val upperBnd = max(s1.bounds.xhi, s2.bounds.xhi)
          val err = max(s1.absError, s2.absError)
          assert(s1.id == s2.id)
          Spec(s1.id, RationalInterval(lowerBnd, upperBnd), err)
        })
  }


  case class Constraint(precondition: Expr, realComp: Expr, finiteComp: Expr, postcondition: Expr) 

  /*  Spec is the overall computed postcondition
    @param kind which approximation type we used
    @param contraints one constraint per path
    @param spec overall computed (merged) specification
  */
  case class Approximation(kind: ApproxKind, constraints: Seq[Constraint], spec: SpecTuple) {
    // one spec per path
    var specsPerPath: Seq[SpecTuple] = Seq.empty
  }

  object FncHandling extends Enumeration {
    type FncHandling = Value
    val Uninterpreted = Value("Uninterpreted")
    val Postcondition = Value("Postcondition")
    val Inlining = Value("Inlining")
  }
  import FncHandling._

  object PathHandling extends Enumeration {
    type PathHandling = Value
    val Pathwise = Value("Pathwise")
    val Merging = Value("Merging")
  }
  import PathHandling._

  object ArithmApprox extends Enumeration {
    type ArithmApprox = Value
    val Z3Only = Value("Z3Only")
    val JustFloat = Value("JustFloat") // evaluate the float. part with xfloat
    val FloatNRange = Value("Float'n'Range") // also replace the real with an approx. of the range
  }
  import ArithmApprox._

  case class ApproxKind(fncHandling: FncHandling.Value, pathHandling: PathHandling.Value, arithmApprox: ArithmApprox.Value) {
    val allowsRealModel = (fncHandling == Uninterpreted && arithmApprox == JustFloat) || // no functions
                          (fncHandling == Inlining && arithmApprox == JustFloat) || // with fncs
                          (fncHandling == Inlining && arithmApprox == Z3Only) // with fncs
  }

  val a_FncIf = List(
    ApproxKind(Uninterpreted, Merging, Z3Only),
    ApproxKind(Uninterpreted, Pathwise, Z3Only),

    ApproxKind(Postcondition, Merging, Z3Only),
    ApproxKind(Postcondition, Merging, JustFloat),
    ApproxKind(Postcondition, Merging, FloatNRange),
    ApproxKind(Postcondition, Pathwise, Z3Only),
    ApproxKind(Postcondition, Pathwise, JustFloat),
    ApproxKind(Postcondition, Pathwise, FloatNRange),
    ApproxKind(Inlining, Merging, Z3Only),
    ApproxKind(Inlining, Merging, JustFloat),
    ApproxKind(Inlining, Merging, FloatNRange),
    ApproxKind(Inlining, Pathwise, Z3Only),
    ApproxKind(Inlining, Pathwise, JustFloat),
    ApproxKind(Inlining, Pathwise, FloatNRange)
    )

  val a_FncNoIf = List(
    ApproxKind(Uninterpreted, Merging, Z3Only),

    ApproxKind(Postcondition, Merging, Z3Only),
    ApproxKind(Postcondition, Merging, JustFloat),
    ApproxKind(Postcondition, Merging, FloatNRange),
    ApproxKind(Inlining, Merging, Z3Only),
    ApproxKind(Inlining, Merging, JustFloat),
    ApproxKind(Inlining, Merging, FloatNRange)
    )


  val a_NoFncIf = List(
    ApproxKind(Uninterpreted, Merging, Z3Only),
    ApproxKind(Uninterpreted, Merging, JustFloat),
    ApproxKind(Uninterpreted, Merging, FloatNRange),
    ApproxKind(Uninterpreted, Pathwise, Z3Only),
    ApproxKind(Uninterpreted, Pathwise, JustFloat),
    ApproxKind(Uninterpreted, Pathwise, FloatNRange)
    )

  val a_NoFncNoIf = List(
    ApproxKind(Uninterpreted, Merging, Z3Only),
    ApproxKind(Uninterpreted, Merging, JustFloat),
    ApproxKind(Uninterpreted, Merging, FloatNRange)
    )


  // approximations are tried in this order
  /*val allApprox = List(
    ApproxKind(Uninterpreted, Merging, Z3Only),
    ApproxKind(Uninterpreted, Merging, JustFloat),
    ApproxKind(Uninterpreted, Merging, FloatNRange),
    ApproxKind(Uninterpreted, Pathwise, Z3Only),
    ApproxKind(Uninterpreted, Pathwise, JustFloat),
    ApproxKind(Uninterpreted, Pathwise, FloatNRange),

    ApproxKind(Postcondition, Merging, Z3Only),
    ApproxKind(Postcondition, Merging, JustFloat),
    ApproxKind(Postcondition, Merging, FloatNRange),
    ApproxKind(Postcondition, Pathwise, Z3Only),
    ApproxKind(Postcondition, Pathwise, JustFloat),
    ApproxKind(Postcondition, Pathwise, FloatNRange),

    ApproxKind(Inlining, Merging, Z3Only),
    ApproxKind(Inlining, Merging, JustFloat),
    ApproxKind(Inlining, Merging, FloatNRange),
    ApproxKind(Inlining, Pathwise, Z3Only),
    ApproxKind(Inlining, Pathwise, JustFloat)
    ApproxKind(Inlining, Pathwise, FloatNRange)
    )
  */

}
