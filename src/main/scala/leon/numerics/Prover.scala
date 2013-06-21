package leon
package numerics

import ceres.common.{Rational, RationalInterval}

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._

import affine.{XFloat, XFloatConfig}
import affine.XFloat._

import Utils._

import Valid._
import ApproximationType._
import Precision._


class Prover(reporter: Reporter, ctx: LeonContext, program: Program, vcMap: Map[FunDef, VerificationCondition], precision: Precision) {
  val verbose = false
  val solver = new NumericSolver(ctx, program)
  val postInliner = new PostconditionInliner(reporter)
  val fullInliner = new FullInliner(reporter, vcMap)

  val unitRoundoff = getUnitRoundoff(precision)

  def check(vc: VerificationCondition) = {
    reporter.info("")
    reporter.info("----------> checking VC of " + vc.funDef.id.name)

    val start = System.currentTimeMillis
    for (c <- vc.allConstraints) {
      reporter.info("----------> checking constraint: " + c.description)
      if (verbose) {println("pre: " + c.pre); println("body: " + c.body); println("post: " + c.post)}

      while (c.hasNextApproximation && !c.solved) {
        val next = c.getNextApproxType.get
        reporter.info("Computing approximation: " + next)
        val approx = getNextApproximation(next, c, vc.inputs)
        c.approximations = c.approximations :+ approx
        c.overrideStatus(checkWithZ3(approx.pre, approx.paths, approx.post, vc.allVariables ++ approx.vars))
        reporter.info("RESULT: " + c.status)
        if (!c.model.isEmpty) reporter.info(c.model.get)

      }
    }

    val totalTime = (System.currentTimeMillis - start)
    vc.verificationTime = Some(totalTime)
  }

  // TODO: we can cache some of the body transforms and reuse for AA...
  def getNextApproximation(tpe: ApproximationType, c: Constraint, inputs: Map[Variable, Record]): ConstraintApproximation = tpe match {
    case Uninterpreted_None =>
      ConstraintApproximation(c.pre, c.body, c.post, Set.empty, tpe)  // nothing with uninterpreted functions

    case PostInlining_None =>
      val (inlinedPre, cnstrPre, varsPre) = postInliner.inlineFncPost(c.pre)
      val (inlinedBody, cnstrBody, varsBody) = postInliner.inlineFncPost(c.body)
      val (inlinedPost, cnstrPost, varsPost) = postInliner.inlineFncPost(c.post)
      ConstraintApproximation(
        And(Seq(inlinedPre) ++ cnstrPre ++ cnstrBody), inlinedBody,
        And(Seq(inlinedPost) ++ cnstrPost), varsBody ++ varsPost ++ varsPre, tpe)

    case PostInlining_AA =>
      val (inlinedBody, cnstrBody, varsBody) = postInliner.inlineFncPost(c.body)
      //val (inlinedPre, cnstrPre, varsPre) = postInliner.inlineFncPost(c.pre)
      val (inlinedPost, cnstrPost, varsPost) = postInliner.inlineFncPost(c.post)

      val (newConstraint, values) = approximatePaths(collectPaths(inlinedBody),
         And(Seq(c.pre) ++ cnstrBody), inputs ++ getVariableRecords(And(cnstrBody) ))
      reporter.info("AA computed: " + newConstraint)


      val cnstr = ConstraintApproximation(newConstraint, BooleanLiteral(true),
         And(Seq(inlinedPost) ++ cnstrPost), varsPost ++ varsBody, tpe)
      cnstr.values = values
      cnstr

    case FullInlining_None =>
      val (inlinedPre, cnstrPre, varsPre) = fullInliner.inlineFncCalls(c.pre)
      val (inlinedBody, cnstrBody, varsBody) = fullInliner.inlineFncCalls(c.body)
      val (inlinedPost, cnstrPost, varsPost) = fullInliner.inlineFncCalls(c.post)

      ConstraintApproximation(
        And(Seq(inlinedPre) ++ cnstrPre), And(inlinedBody, And(cnstrPost ++ cnstrBody)), //cntrs are the function bodies
        And(Seq(inlinedPost)), varsBody ++ varsPost ++ varsPre, tpe)


    case FullInlining_AA =>
      //TODO: val (inlinedPre, cnstrPre, varsPre) = fullInliner.inlineFncCalls(c.pre)
      val (inlinedBody, cnstrBody, varsBody) = fullInliner.inlineFncCalls(c.body)
      val (inlinedPost, cnstrPost, varsPost) = fullInliner.inlineFncCalls(c.post) // cntrs are the function bodies

      // we need to approximate the body
      val newBody = And(And(cnstrBody ++ cnstrPost), inlinedBody)

      println("new body: " + newBody)
      val (newConstraint, values) = approximatePaths(collectPaths(newBody),
        c.pre, inputs) //add varsPost?
      reporter.info("AA computed: " + newConstraint)

      val cnstr = ConstraintApproximation(newConstraint, BooleanLiteral(true), And(Seq(inlinedPost)), varsPost ++ varsBody, tpe)
      cnstr.values = values
      cnstr

      // TODO: If neither work, do partial approx.
    }

  /*def addSpecs(vc: VerificationCondition): VerificationCondition = {
    //val start = System.currentTimeMillis
    // if there are constraints, then those have already been handled, only deal with VCs without post
    if(!vc.specConstraint.get.approximated) {
      //computeApproximation(vc.specConstraint.get, vc.inputs)
    }

    //val totalTime = (System.currentTimeMillis - start)
    //vc.verificationTime = Some(totalTime)
    vc
  }*/



  private def checkWithZ3(pre: Expr, paths: Set[Path], post: Expr, variables: Seq[Variable]): (Option[Valid], Option[Map[Identifier, Expr]]) = {
    val (resVar, eps, buddies) = getVariables(variables)
    val trans = new NumericConstraintTransformer(buddies, resVar, eps, RoundoffType.RoundoffMultiplier, reporter)

    var (realPart, noisyPart) = (Seq[Expr](), Seq[Expr]())

    for(path <- paths) {
      // TODO: check that this does not fail if we have just one expression
      val (r, n) = trans.transformBlock(And(path.expression))
      realPart = realPart :+ And(path.condition, r)
      noisyPart = noisyPart :+ And(trans.getNoisyCondition(path.condition), n)
    }

    val precondition = trans.transformCondition(pre)
    val postcondition = trans.transformCondition(post)

    val body = if(realPart.isEmpty && noisyPart.isEmpty) BooleanLiteral(true)
      else if(!realPart.isEmpty && !noisyPart.isEmpty) And(Or(realPart), Or(noisyPart))
      else {
        reporter.error("one of realPart or noisyPart is empty")
        BooleanLiteral(true)
      }
    // This is to make Z3 gives us also the error
    // TODO: maybe also add this for the input variables?
    val resultError = Equals(getNewResErrorVariable, Minus(resVar, buddies(resVar)))
    val machineEpsilon = Equals(eps, RationalLiteral(unitRoundoff))
    val toCheck = Implies(And(precondition, And(body, And(resultError, machineEpsilon))), postcondition)
    println("toCheck: " + toCheck)

    // If precondition is false, we'll prove anything, so don't try to prove at all
    if (reporter.errorCount == 0 && sanityCheck(precondition, body)) {
      val (valid, model) = solver.checkValid(toCheck)
      (Some(valid), model)
    } else
      (None, None)
  }


  /*private def computeApproximation(c: Constraint, inputs: Map[Variable, Record]) = {
    for (path <- c.paths) {
      val pathCondition = And(path.condition, filterPreconditionForBoundsIteration(c.pre))
      if (sanityCheck(pathCondition)) {  // If this implies false, range tightening fails
        // The condition given to the solver is the real(ideal)-valued one, since we use Z3 for the real part only.
        val (variables, indices) = variables2xfloats(inputs, solver, pathCondition)
        path.values = inXFloats(path.expression, variables, solver, pathCondition) -- inputs.keys
        path.indices= indices

      } else {
        reporter.warning("skipping path " + path)
        // TODO: what to do here? we only checked the ideal part is impossible,
        // but the floating-point part may still be possible
        // although this would be quite the strange scenario...
      }
    }
    c.approximated = true
  }*/

  /*private def computeApproximation(c: ConstraintApproximation, inputs: Map[Variable, Record]) = {
    for (path <- c.paths) {
      val pathCondition = And(path.condition, filterPreconditionForBoundsIteration(c.pre))
      if (sanityCheck(pathCondition)) {  // If this implies false, range tightening fails
        // The condition given to the solver is the real(ideal)-valued one, since we use Z3 for the real part only.
        val (variables, indices) = variables2xfloats(inputs, solver, pathCondition)
        path.values = inXFloats(path.expression, variables, solver, pathCondition) -- inputs.keys
        println("path values: " + path.values)
        path.indices= indices

      } else {
        reporter.warning("skipping path " + path)
        // TODO: what to do here? we only checked the ideal part is impossible,
        // but the floating-point part may still be possible
        // although this would be quite the strange scenario...
      }
    }
    //c.approximated = true
  }*/

  private def computeApproximation(paths: Set[Path], precondition: Expr, inputs: Map[Variable, Record]) = {
    for (path <- paths) {
      val pathCondition = And(path.condition, filterPreconditionForBoundsIteration(precondition))
      if (sanityCheck(pathCondition)) {  // If this implies false, range tightening fails
        // The condition given to the solver is the real(ideal)-valued one, since we use Z3 for the real part only.
        val config = XFloatConfig(solver, pathCondition, unitRoundoff)
        val (variables, indices) = variables2xfloats(inputs, config)
        path.values = inXFloats(path.expression, variables, config) -- inputs.keys
        println("path values: " + path.values)
        path.indices= indices

      } else {
        reporter.warning("skipping path " + path)
        // TODO: what to do here? we only checked the ideal part is impossible,
        // but the floating-point part may still be possible
        // although this would be quite the strange scenario...
      }
    }
  }

  // Computes one constraint that overapproximates the paths given.
  private def approximatePaths(paths: Set[Path], pre: Expr, inputs: Map[Variable, Record]): (Expr, Map[Expr, (RationalInterval, Rational)]) = {
    computeApproximation(paths, pre, inputs)
    println("approximation: " + paths.head.values)
    val approx = mergeRealPathResults(paths)
    println("merged: " + approx)
    val newConstraint = constraintFromResults(approx)
    (newConstraint, approx)
  }

 /* private def approximateConstraint(c: Constraint, inputs: Map[Variable, Record]): Expr = {
    computeApproximation(c, inputs)
    val approx = mergeRealPathResults(c.paths)
    val newConstraint = constraintFromResults(approx)
    newConstraint
  }*/

  /*private def approximateConstraint(c: ConstraintApproximation, inputs: Map[Variable, Record]): Expr = {
    computeApproximation(c, inputs)
    val approx = mergeRealPathResults(c.paths)
    val newConstraint = constraintFromResults(approx)
    newConstraint
  }*/




  // Returns a map from all variables to their final value, including local vars
  private def inXFloats(exprs: List[Expr], vars: Map[Expr, XFloat], config: XFloatConfig): Map[Expr, XFloat] = {
    var currentVars: Map[Expr, XFloat] = vars

    for (expr <- exprs) expr match {
      case Equals(variable, value) =>
        try {
          currentVars = currentVars + (variable -> eval(value, currentVars, config))
        } catch {
          case UnsupportedFragmentException(msg) => reporter.error(msg)
        }

      case BooleanLiteral(true) => ;
      case _ =>
        reporter.error("AA cannot handle: " + expr)
    }

    currentVars
  }

  // Evaluates an arithmetic expression
  private def eval(expr: Expr, vars: Map[Expr, XFloat], config: XFloatConfig): XFloat = expr match {
    case v @ Variable(id) => vars(v)
    case RationalLiteral(v) => XFloat(v, config)
    case IntLiteral(v) => XFloat(v, config)
    case UMinus(rhs) => - eval(rhs, vars, config)
    case Plus(lhs, rhs) => eval(lhs, vars, config) + eval(rhs, vars, config)
    case Minus(lhs, rhs) => eval(lhs, vars, config) - eval(rhs, vars, config)
    case Times(lhs, rhs) => eval(lhs, vars, config) * eval(rhs, vars, config)
    case Division(lhs, rhs) => eval(lhs, vars, config) / eval(rhs, vars, config)
    case Sqrt(t) => eval(t, vars, config).squareRoot
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
        //reporter.info("Sanity check passed! :-)")
        true
      case _ =>
        reporter.warning("Sanity check failed! ")// + sanityCondition)
        false
    }

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


  // Overrides the status with new result
  /*private def checkConstraint(c: Constraint, variables: Seq[Variable]) = {
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
      c.status = Some(valid)
      c.model = model
    }
  }*/

  /*private def approximateConstraint(c: Constraint, inputs: Map[Variable, Record]): Constraint = {
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
  }*/
}
