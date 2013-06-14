package leon
package numerics

import ceres.common.{Rational, RationalInterval}

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._

import affine.XFloat
import affine.XFloat._

import Valid._

class Prover(reporter: Reporter, ctx: LeonContext, program: Program) {
  val verbose = true
  val solver = new NumericSolver(ctx, program)

  def check(vc: VerificationCondition) = {
    reporter.info("")
    reporter.info("----------> checking VC of " + vc.funDef.id.name)

    val start = System.currentTimeMillis
    for (c <- vc.toCheck) {
      if (verbose) {println("pre: " + c.pre); println("body: " + c.body); println("post: " + c.post)}

      c.paths = collectPaths(c.body)

      // First try Z3 alone
      /*val (res, model) = checkConstraint(c, vc.allVariables)
      reporter.info("Z3 only result: " + res)
      c.status = res
      c.model = model
      */
      // If Z3 failed ...
      c.status match {
        case (None | Some(DUNNO) | Some(NOT_SURE)) =>
          // ... try XFloat alone
          val approxConstraint = approximateConstraint(c, vc.inputs)
          val (resAA, modelAA) = checkConstraint(approxConstraint, vc.allVariables)
          println("XFloat only result: " + resAA)
          c.status = resAA
          c.model = modelAA
        case _ =>;
      }

      // TODO: If neither work, do partial approx.

    }

    val totalTime = (System.currentTimeMillis - start)
    vc.verificationTime = Some(totalTime)
  }

  private def checkConstraint(c: Constraint, variables: Seq[Variable]): (Option[Valid], Option[Map[Identifier, Expr]]) = {
    val (resVar, eps, buddies) = getVariables(variables)
    val trans = new NumericConstraintTransformer(buddies, resVar, eps, RoundoffType.RoundoffMultiplier, reporter)

    var realPart: Seq[Expr] = Seq.empty
    var noisyPart: Seq[Expr] = Seq.empty

    for(path <- c.paths) {
      val (r, n) = trans.transformBlock(And(path.expression))
      realPart = realPart :+ And(path.condition, r)
      noisyPart = noisyPart :+ And(trans.getNoisyCondition(path.condition), n)
    }

    val precondition = trans.transformCondition(c.pre)
    val postcondition = trans.transformCondition(c.post)

    val body = if(realPart.isEmpty && noisyPart.isEmpty) BooleanLiteral(true)
      else if(!realPart.isEmpty && !noisyPart.isEmpty) And(Or(realPart), Or(noisyPart))
      else {
        reporter.error("one of realPart or noisyPart is empty")
        BooleanLiteral(true)
      }
    val toCheck = Implies(And(precondition, body), postcondition)
    println("toCheck: " + toCheck)

    // If precondition is false, we'll prove anything, so don't try to prove at all
    if (reporter.errorCount == 0 && sanityCheck(precondition, body)) {
      val (valid, model) = solver.checkValid(toCheck)
      (Some(valid), model)
    } else {
      (None, None)
    }
  }

  // TODO: approximatePath


  private def approximateConstraint(c: Constraint, inputs: Map[Variable, Record]): Constraint = {
    reporter.info("Now trying with XFloat only...")

    val paths = c.paths.map(p => p.addCondition(filterPreconditionForBoundsIteration(c.pre)))
    //println("paths: \n" + paths.mkString("\n"))

    for (path <- paths) {
      if (sanityCheck(path.condition)) {  // If this implies false, range tightening fails

        // The condition given to the solver is the real(ideal)-valued one, since we use Z3 for the real part only.
        val (variables, indices) = variables2xfloats(inputs, solver, path.condition)
        path.values = inXFloats(path.expression, variables, solver, path.condition) -- inputs.keys

      } else {
        reporter.warning("skipping path " + path)
        // TODO: what to do here? we only checked the ideal part is impossible,
        // but the floating-point part may still be possible
        // although this would be quite the strange scenario...
      }
    }

    val approx = mergePathResults(paths)
    val newConstraint = constraintFromResults(approx)
    Constraint(And(c.pre, newConstraint), BooleanLiteral(true), c.post)
  }


  // Returns a map from all variables to their final value, including local vars
  private def inXFloats(exprs: List[Expr], vars: Map[Expr, XFloat], solver: NumericSolver, pre: Expr): Map[Expr, XFloat] = {
    var currentVars: Map[Expr, XFloat] = vars

    for (expr <- exprs) expr match {
      case Equals(variable, value) =>
        try {
          currentVars = currentVars + (variable -> eval(value, currentVars, solver, pre))
          } catch {
            case UnsupportedFragmentException(msg) => reporter.error(msg)
          }

      case _ =>
        reporter.error("AA cannot handle: " + expr)
    }

    currentVars
  }

  // Evaluates an arithmetic expression
  private def eval(expr: Expr, vars: Map[Expr, XFloat], solver: NumericSolver, pre: Expr): XFloat = expr match {
    case v @ Variable(id) => vars(v)
    case RationalLiteral(v) => XFloat(v, solver, pre)
    case IntLiteral(v) => XFloat(v, solver, pre)
    case UMinus(rhs) => - eval(rhs, vars, solver, pre)
    case Plus(lhs, rhs) => eval(lhs, vars, solver, pre) + eval(rhs, vars, solver, pre)
    case Minus(lhs, rhs) => eval(lhs, vars, solver, pre) - eval(rhs, vars, solver, pre)
    case Times(lhs, rhs) => eval(lhs, vars, solver, pre) * eval(rhs, vars, solver, pre)
    case Division(lhs, rhs) => eval(lhs, vars, solver, pre) / eval(rhs, vars, solver, pre)
    case Sqrt(t) => eval(t, vars, solver, pre).squareRoot
    case _ =>
      throw UnsupportedFragmentException("AA cannot handle: " + expr)
      null
  }


  // if true, we're sane
  private def sanityCheck(pre: Expr, body: Expr = BooleanLiteral(true)): Boolean = {
    val sanityCondition = Implies(And(pre, body), BooleanLiteral(false))
    solver.checkValid(sanityCondition) match {
      case (VALID, model) =>
        reporter.warning("Not sane! " + sanityCondition)
        false
      case (INVALID, model) =>
        true
      case _ =>
        reporter.error("Sanity check failed! " + sanityCondition)
        false
    }

  }

  /*
    Consolidates results from different paths by merging the intervals and finding the largest error.
   */
  private def mergePathResults(paths: Set[Path]): Map[Expr, (RationalInterval, Rational)] = {
    import Rational._

    var collection: Map[Expr, List[XFloat]] = Map.empty
    for (path <- paths) {
      for ((k, v) <- path.values) {
        collection = collection + ((k, List(v) ++ collection.getOrElse(k, List())))
      }
    }

    // Two options:
    // interval -> ranges of ACTUAL variables  (but in this case, the key is the buddy variable!)
    // realInterval -> ranges of IDEAL variables
    var resMap: Map[Expr, (RationalInterval, Rational)] = Map.empty
    for ((k, list) <- collection) {
      var lo = list.head.realInterval.xlo
      var hi = list.head.realInterval.xhi
      var err = list.head.maxError

      for (xf <- list.tail) {
        lo = min(lo, xf.realInterval.xlo)
        hi = max(hi, xf.realInterval.xhi)
        err = max(err, xf.maxError)
      }
      resMap = resMap + ((k, (RationalInterval(lo, hi), err)))
    }
    resMap
  }

  private def constraintFromResults(results: Map[Expr, (RationalInterval, Rational)]): Expr = {
    And(results.foldLeft(Seq[Expr]())(
      (seq, kv) => seq ++ Seq(LessEquals(RationalLiteral(kv._2._1.xlo), kv._1),
                                  LessEquals(kv._1, RationalLiteral(kv._2._1.xhi)),
                                  Noise(kv._1, RationalLiteral(kv._2._2)))))
  }


  private def collectPaths(expr: Expr): Set[Path] = expr match {
    case IfExpr(cond, then, elze) =>
      val thenPaths = collectPaths(then).map(p => p.addCondition(cond))
      val elzePaths = collectPaths(elze).map(p => p.addCondition(negate(cond)))

      thenPaths ++ elzePaths

    case And(args) =>
      var currentPaths: Set[Path] = collectPaths(args.head)

      for (a <- args.tail) {
        var newPaths: Set[Path] = Set.empty

        val nextPaths = collectPaths(a)

        // TODO: in one loop?
        for (np <- nextPaths) {
          for (cp <- currentPaths) {
            newPaths = newPaths + cp.addPath(np)
          }
        }
        currentPaths = newPaths
      }
      currentPaths

    case Equals(e, f) =>
      collectPaths(f).map(p => p.addEqualsToLast(e))

    case _ =>
      Set(Path(BooleanLiteral(true), List(expr)))
  }

  private def getVariables(variables: Seq[Variable]): (Variable, Variable, Map[Expr, Expr]) = {
    val resVar = Variable(FreshIdentifier("#ress")).setType(RealType)
    val machineEps = Variable(FreshIdentifier("#eps")).setType(RealType)

    var buddies: Map[Expr, Expr] =
      variables.foldLeft(Map[Expr, Expr](resVar -> Variable(FreshIdentifier("#res_0")).setType(RealType)))(
        (map, nextVar) => map + (nextVar -> Variable(FreshIdentifier("#"+nextVar.id.name+"_0")).setType(RealType))
      )
    (resVar, machineEps, buddies)
  }


  private def filterPreconditionForBoundsIteration(expr: Expr): Expr = expr match {
    case And(args) => And(args.map(a => filterPreconditionForBoundsIteration(a)))
    case Noise(e, f) => BooleanLiteral(true)
    case Roundoff(e) => BooleanLiteral(true)
    case _ => expr
  }
}
