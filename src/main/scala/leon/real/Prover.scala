/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import purescala.Trees._
import purescala.Definitions._
import purescala.TreeOps._

import real.Trees.{Noise, Roundoff, Actual, RealLiteral, RelError, WithIn}
import real.TreeOps._
import Sat._
import Approximations._
import FncHandling._
import ArithmApprox._
import PathHandling._
import Rational._

object Prover {
  /*
    Performs some pre-processing of the constraint in order to increase solving success.
    - equality propagation
    - removing of redundant bounds constraints (included in another)
  */
  def simplifyConstraint(e: Expr, removeBounds: Boolean = true, equalityPropagation: Boolean = true): Expr = {
    // for bounds, first collect all bounds, then re-generate constraints
    val (boundsConstraint, remainder) = if (removeBounds) {
      val boundsCollector = new TightBoundsCollector
      val rem = boundsCollector.transform(e)
      (And(boundsCollector.getConstraints), rem)
    } else {
      (True, e)
    }

    if (equalityPropagation) {
      // for equality propagation, replace variables by their definition
      val equalsPropagator = new EqualsPropagator
      val equalities = equalsPropagator.transform(remainder)
      And(boundsConstraint, equalities)
    } else {
      And(boundsConstraint, remainder)
    }
  }


  private class EqualsPropagator extends TransformerWithPC {
    type C = Map[Expr, Expr]
    val initC = Map[Expr, Expr]()

    def register(e: Expr, path: Map[Expr, Expr]): Map[Expr, Expr] = e match {
      case Equals(v @ Variable(id), expr) => path + (v -> replace(path, expr))
      case _ => path
    }

    override def rec(e: Expr, path: Map[Expr, Expr]): Expr = e match {
      case Equals(v, expr) =>
        Equals(v, replace(path, expr))
      case _ =>
        super.rec(e, path)
    }
  }


  private class TightBoundsCollector extends TransformerWithPC {
    type C = Seq[Expr]
    val initC = Nil

    case class Bound(loEq: Option[Rational], lo: Option[Rational], up: Option[Rational], upEq: Option[Rational], absUncert: Option[Rational], relUncert: Option[Rational]) {
      // update to tightest bounds
      def updateLoEqTight(n: Rational): Bound = {
        if (loEq.nonEmpty) Bound(Some(max(n, loEq.get)), lo, up, upEq, absUncert, relUncert)
        else Bound(Some(n), lo, up, upEq, absUncert, relUncert)
      }
      def updateLoTight(n: Rational): Bound = {
        if (lo.nonEmpty) Bound(loEq, Some(max(n, lo.get)), up, upEq, absUncert, relUncert)
        else Bound(loEq, Some(n), up, upEq, absUncert, relUncert)
      }
      def updateUpTight(n: Rational): Bound = {
        if (up.nonEmpty) Bound(loEq, lo, Some(min(n, up.get)), upEq, absUncert, relUncert)
        else Bound(loEq, lo, Some(n), upEq, absUncert, relUncert)
      }
      def updateUpEqTight(n: Rational): Bound = {
        if (upEq.nonEmpty) Bound(loEq, lo, up, Some(min(n, upEq.get)), absUncert, relUncert)
        else Bound(loEq, lo, up, Some(n), absUncert, relUncert)
      }
      def updateAbsUncertTight(n: Rational): Bound = {
        if (absUncert.nonEmpty) Bound(loEq, lo, up, upEq, Some(min(n, absUncert.get)), relUncert)
        else Bound(loEq, lo, up, upEq, Some(n), relUncert)
      }
      def updateRelUncertTight(n: Rational): Bound = {
        if (relUncert.nonEmpty) Bound(loEq, lo, up, upEq, absUncert, Some(min(n, relUncert.get)))
        else Bound(loEq, lo, up, upEq, absUncert, Some(n))
      }
    }
    val emptyBound = Bound(None, None, None, None, None, None)

    // indexed by variable
    var boundMap = Map[Expr, Bound]()

    def register(e: Expr, path: C): C = path :+ e

    // (Sound) Overapproximation in the case of strict inequalities
    // Removes the recorded constraints
    override def rec(e: Expr, path: C): Expr = e match {
      case LessEquals(RealLiteral(lwrBnd), x @ Variable(_)) => // a <= x
        boundMap += (x -> boundMap.getOrElse(x, emptyBound).updateLoEqTight(lwrBnd)); True

      case LessEquals(x @ Variable(_), RealLiteral(uprBnd)) => // x <= b
        boundMap += (x -> boundMap.getOrElse(x, emptyBound).updateUpEqTight(uprBnd)); True

      case LessThan(RealLiteral(lwrBnd), x @ Variable(_)) => // a < x
        boundMap += (x -> boundMap.getOrElse(x, emptyBound).updateLoTight(lwrBnd)); True

      case LessThan(x @ Variable(_), RealLiteral(uprBnd)) => // x < b
        boundMap += (x -> boundMap.getOrElse(x, emptyBound).updateUpTight(uprBnd)); True

      case GreaterEquals(RealLiteral(uprBnd), x @ Variable(_)) => // b >= x
        boundMap += (x -> boundMap.getOrElse(x, emptyBound).updateUpEqTight(uprBnd)); True

      case GreaterEquals(x @ Variable(_), RealLiteral(lwrBnd)) => // x >= a
        boundMap += (x -> boundMap.getOrElse(x, emptyBound).updateLoEqTight(lwrBnd)); True

      case GreaterThan(RealLiteral(uprBnd), x @ Variable(_)) => // b > x
        boundMap += (x -> boundMap.getOrElse(x, emptyBound).updateUpTight(uprBnd)); True

      case GreaterThan(x @ Variable(_), RealLiteral(lwrBnd)) => // x > a
        boundMap += (x -> boundMap.getOrElse(x, emptyBound).updateLoTight(lwrBnd)); True

      case Noise(x @ Variable(_), RealLiteral(value)) =>
        boundMap += (x -> boundMap.getOrElse(x, emptyBound).updateAbsUncertTight(value)); True

      case Noise(_, _) =>
        throw UnsupportedRealFragmentException(e.toString); True

      case RelError(x @ Variable(id), RealLiteral(value)) =>
        boundMap += (x -> boundMap.getOrElse(x, emptyBound).updateRelUncertTight(value)); True

      case WithIn(x @ Variable(_), lwrBnd, upBnd) =>
        boundMap += (x -> boundMap.getOrElse(x, emptyBound).updateLoTight(lwrBnd).updateUpTight(upBnd)); True

      case WithIn(e, lwrBnd, upBnd) =>
        throw UnsupportedRealFragmentException(e.toString); True

      case Or(_) | Not(_) =>
        throw new Exception("OR and NOT are not allowed when computing bounds"); e

      case i: IfExpr => i
      case _ =>
        super.rec(e, path)

    }

    def getConstraints: Seq[Expr] = {
      boundMap.map({
        case (v, Bound(loEq, lo, up, upEq, absUncert, relUncert)) =>
          var cnstrs = Seq[Expr]()
          if (loEq.nonEmpty) cnstrs :+= LessEquals(RealLiteral(loEq.get), v)
          if (lo.nonEmpty) cnstrs :+= LessThan(RealLiteral(lo.get), v)

          if (up.nonEmpty) cnstrs :+= LessThan(v, RealLiteral(up.get))
          if (upEq.nonEmpty) cnstrs :+= LessEquals(v, RealLiteral(upEq.get))

          if (absUncert.nonEmpty) cnstrs :+= Noise(v, RealLiteral(absUncert.get))
          if (relUncert.nonEmpty) cnstrs :+= RelError(v, RealLiteral(relUncert.get))
          (v -> And(cnstrs))
        }).values.toSeq
    }

  }

}

class Prover(ctx: LeonContext, options: RealOptions, prog: Program, fncs: Map[FunDef, Fnc]) {
  import Prover._
  implicit val debugSection = DebugSectionVerification
  val reporter = ctx.reporter
  val solver = new RealSolver(ctx, prog, options.z3Timeout)

  def getApplicableApproximations(vcs: Seq[VerificationCondition]): Map[VerificationCondition, List[ApproxKind]] =
    vcs.map { vc =>
        val list = (
          if (vc.allFncCalls.isEmpty) {
            if (containsIfExpr(vc.body))
              if (options.pathError) a_NoFncIf.filter(ak => ak.pathHandling == Merging)
              else a_NoFncIf
            else a_NoFncNoIf
          } else {
            if (containsIfExpr(vc.body))
              if (options.pathError) a_FncIf.filter(ak => ak.pathHandling == Merging)
              else a_FncIf
            else a_FncNoIf
          })

        if (!options.z3Only) (vc, list.filter(ak => ak.arithmApprox != Z3Only))
        else (vc, list)
      }.toMap

  // Returns the precision with which we can satisfy all constraints, or the last one tried,
  // as well as an indication whether verification was successfull.
  def check(vcs: Seq[VerificationCondition]): (Precision, Boolean) = {
    val validApproximations = getApplicableApproximations(vcs)

    val precisions = options.precision

    def findPrecision(lowerBnd: Int, upperBnd: Int): (Precision, Boolean) = {
      if (lowerBnd > upperBnd) (precisions.last, false)
      else {
        val mid = lowerBnd + (upperBnd - lowerBnd) / 2// ceiling int division
        reporter.info("Checking precision: " + precisions(mid))
        if (checkVCsInPrecision(vcs, precisions(mid), validApproximations)) {
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
    validApproximations.foreach(x => reporter.debug(x._1 + ": " + x._2))

    findPrecision(0, precisions.length - 1)
  }

  def checkVCsInPrecision(vcs: Seq[VerificationCondition], precision: Precision,
    validApproximations: Map[VerificationCondition, List[ApproxKind]]): Boolean = {
    var postMap: Map[FunDef, Option[Spec]] = vcs.map(vc => (vc.funDef -> None)).toMap

    //println("checking vcs: ")

    for (vc <- vcs if (options.specGen || vc.kind != VCKind.SpecGen)) {
      reporter.info("Verification condition  ==== %s (%s) ====".format(vc.fncId, vc.kind))
      reporter.debug("pre: " + vc.pre)
      reporter.debug("body: " + vc.body)
      reporter.debug("post: " + vc.post)

      val start = System.currentTimeMillis
      var spec: Option[Spec] = None

      val approximations = validApproximations(vc)

      approximations.find(aKind => {
        reporter.info("approx: " + aKind)

        try {
          val currentApprox = getApproximation(vc, aKind, precision, postMap)
          spec = merge(spec, currentApprox.spec)
          postMap += (vc.funDef -> currentApprox.spec)

          if (vc.kind == VCKind.SpecGen) true  // specGen, no need to check, only uses first approximation
          else
            checkValid(currentApprox, vc.variables, precision) match {
              case Some(true) =>
                reporter.info("==== VALID ====")
                vc.value += (precision -> Some(true))
                true
              case Some(false) =>
                reporter.info("=== INVALID ===")
                vc.value += (precision -> Some(false))
                true
              case None =>
                reporter.info("---- Unknown ----")
                false
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
          case UnsoundBoundsException(msg) =>
            reporter.error(msg)
            return false

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

    vcs.forall( vc => vc.kind == VCKind.SpecGen || !vc.value(precision).isEmpty )
  }

  def checkValid(app: Approximation, variables: VariablePool, precision: Precision): Option[Boolean] = {
    reporter.debug("checking for valid: " + app.constraints)

    val transformer = new LeonToZ3Transformer(variables, precision)
    var validCount = 0
    var invalidCount = 0

    for ((cnstr, index) <- app.constraints.zipWithIndex) {
      val realCnstr = addResult(cnstr.realComp, Some(variables.resultVar))
      val finiteCnstr = addResultF(cnstr.finiteComp, Some(variables.fResultVar))

      val sanityConstraint = And(cnstr.precondition, And(realCnstr, finiteCnstr))
      val toCheck = And(sanityConstraint, negate(cnstr.postcondition))

      println("\ntoCheck before: ")
      println(toCheck)

      println("\nsimplified: ")
      println(simplifyConstraint(toCheck))


      val z3constraint = massageArithmetic(transformer.getZ3Expr(toCheck))
      val sanityExpr = massageArithmetic(transformer.getZ3Expr(sanityConstraint))




      reporter.debug("z3constraint ("+index+"): " + z3constraint)

      if (reporter.errorCount == 0 && sanityCheck(sanityExpr)) {
        solver.checkSat(z3constraint) match {
          case (UNSAT, _) =>
            reporter.info(s"Constraint with $index is valid.")
            validCount += 1
          case (SAT, model) =>
            if (app.kind.allowsRealModel) {
              // Idea: check if we get a counterexample for the real part only, that is then a possible counterexample, (depends on the approximation)
              val realFilter = new RealFilter
              val realOnlyConstraint = realFilter.transform(And(And(cnstr.precondition, realCnstr), negate(cnstr.postcondition)))
              val massaged = massageArithmetic(transformer.getZ3Expr(realOnlyConstraint))
              solver.checkSat(massaged) match {
                case (SAT, model) =>
                  reporter.info("counterexample: " + model)
                  invalidCount += 1
                case (UNSAT, _) =>
                case _ =>
              }
            } else {
              reporter.info(s"Constraint with $index is unknown.")
            }


          case _ =>;
        }
      }
    }
    if ( (validCount + invalidCount) < app.constraints.length) None
    else if (invalidCount > 0) Some(false)
    else Some(true)
  }



  // DOC: we only support function calls in fnc bodies, not in pre and post
  def getApproximation(vc: VerificationCondition, kind: ApproxKind, precision: Precision, postMap: Map[FunDef, Option[Spec]]): Approximation = {
    val postInliner = new PostconditionInliner(precision, postMap)
    val fncInliner = new FunctionInliner(fncs)
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

    val (pre, bodyFnc, post) = kind.fncHandling match {
      case Uninterpreted => (vc.pre, vc.body, vc.post)
      case Postcondition => (vc.pre, postInliner.transform(vc.body), vc.post)
      case Inlining => (vc.pre, fncInliner.transform(vc.body), vc.post)
    }
    reporter.debug("after FNC handling:\npre: %s\nbody: %s\npost: %s".format(pre,bodyFnc,post))


    val paths: Set[Path] = kind.pathHandling match {
      case Pathwise => getPaths(bodyFnc).map {
        case (cond, expr) => Path(cond, expr, idealToActual(expr, vc.variables))
      }
      case Merging =>  Set(Path(True, bodyFnc, idealToActual(bodyFnc, vc.variables)))
    }
    reporter.debug("after PATH handling:\nbody: %s".format(paths.mkString("\n")))


    kind.arithmApprox match {
      case Z3Only =>
        var constraints = Seq[Constraint]()
        for (path <- paths) {
          constraints :+= Constraint(And(pre, path.condition), path.bodyReal, path.bodyFinite, post)
        }
        Approximation(kind, constraints, None)

      case JustFloat =>
        var constraints = Seq[Constraint]()
        var specsPerPath = Seq[Option[Spec]]()
        var spec: Option[Spec] = None

        for ( path <- paths if (isFeasible(And(pre, path.condition))) ) {
          //solver.clearCounts
          val transformer = new Approximator(reporter, solver, precision, And(pre, path.condition), vc.variables, options.pathError)
          val (bodyFiniteApprox, nextSpec) = transformer.transformWithSpec(path.bodyFinite, vc.kind == VCKind.Precondition)
          //println("solver counts: " + solver.getCounts)
          spec = merge(spec, nextSpec)
          //if(!nextSpec.isEmpty)
          specsPerPath :+= nextSpec//.get// else specsPerPath :+= DummySpec
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
                (cnstr, spec) <- approx.constraints.zip(approx.specsPerPath)
              ) yield
                Constraint(cnstr.precondition, specToRealExpr(spec), cnstr.finiteComp, cnstr.postcondition)
            Approximation(kind, newConstraints, approx.spec)
          case None =>
            throw new RealArithmeticException("Cannot compute Float'n'Range approximation because JustFloat approximation is missing.")
            null
        }
    }
  }

  private def merge(currentSpec: Option[Spec], newSpec: Option[Spec]): Option[Spec] = (currentSpec, newSpec) match {
    case (Some(s1), Some(s2)) =>
      val lowerBnd = min(s1.bounds.xlo, s2.bounds.xlo)
      val upperBnd = max(s1.bounds.xhi, s2.bounds.xhi)
      val err = max(s1.absError, s2.absError)
      assert(s1.id == s2.id)
      Some(Spec(s1.id, RationalInterval(lowerBnd, upperBnd), err))
    case (None, Some(s)) => newSpec
    case _ => currentSpec
  }

  // if true, we're sane
  private def sanityCheck(pre: Expr, body: Expr = BooleanLiteral(true)): Boolean = {
    val sanityCondition = And(pre, body)
    solver.checkSat(sanityCondition) match {
      case (SAT, model) => true
      case (UNSAT, model) =>
        reporter.warning("Not sane! " + sanityCondition)
        false
      case _ =>
        reporter.info("Sanity check failed! ")// + sanityCondition)
        false
    }
  }




}
