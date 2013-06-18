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

import Utils._

import Valid._



class Prover(reporter: Reporter, ctx: LeonContext, program: Program) {
  val verbose = false
  val solver = new NumericSolver(ctx, program)

  def check(vc: VerificationCondition) = {
    reporter.info("")
    reporter.info("----------> checking VC of " + vc.funDef.id.name)

    val start = System.currentTimeMillis
    for (c <- vc.allConstraints) {
      reporter.info("----------> checking constraint: " + c.description)
      if (verbose) {println("pre: " + c.pre); println("body: " + c.body); println("post: " + c.post)}

      while (c.hasNextApproximation && !c.solved) {
        c.getNextApproximation match {
          case Some(cnstr) =>
            reporter.info("Attempting approximation: " + cnstr.name)
            c.overrideStatus(checkWithZ3(cnstr.pre, cnstr.paths, cnstr.post, vc.allVariables))
            reporter.info("RESULT: " + c.status)
          case None =>;
        }
      }
    }

    val totalTime = (System.currentTimeMillis - start)
    vc.verificationTime = Some(totalTime)
  }




  def addSpecs(vc: VerificationCondition): VerificationCondition = {
    //val start = System.currentTimeMillis
    // if there are constraints, then those have already been handled, only deal with VCs without post
    if(!vc.specConstraint.get.approximated) {
      computeApproximation(vc.specConstraint.get, vc.inputs)
    }

    //val totalTime = (System.currentTimeMillis - start)
    //vc.verificationTime = Some(totalTime)
    vc
  }



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
    // This is make Z3 gives us also the error
    // TODO: maybe also add this for the input variables?
    val resultError = Equals(getNewResErrorVariable, Minus(resVar, buddies(resVar)))
    val toCheck = Implies(And(precondition, And(body, resultError)), postcondition)
    println("toCheck: " + toCheck)

    // If precondition is false, we'll prove anything, so don't try to prove at all
    if (reporter.errorCount == 0 && sanityCheck(precondition, body)) {
      val (valid, model) = solver.checkValid(toCheck)
      (Some(valid), model)
    } else
      (None, None)
  }


  private def computeApproximation(c: Constraint, inputs: Map[Variable, Record]) = {
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
  }

  private def approximateConstraint(c: Constraint, inputs: Map[Variable, Record]): Expr = {
    computeApproximation(c, inputs)
    val approx = mergeRealPathResults(c.paths)
    val newConstraint = constraintFromResults(approx)
    newConstraint
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
