package leon
package numerics

import ceres.common.{Rational, RationalInterval}

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._

import affine.XFloat
import affine.XFloat._

import Valid._
import Utils._

class Prover(reporter: Reporter, ctx: LeonContext, program: Program) {
  val verbose = true
  val absTransform = new AbsTransformer
  val solver = new NumericSolver(ctx, program)

  def check(vc: VerificationCondition) = {
    reporter.info("----------> checking VC of " + vc.funDef.id.name)

    val start = System.currentTimeMillis
    for (constr <- vc.toCheck) {
      println("pre: " + constr.pre)
      println("body: " + constr.body)
      println("post: " + constr.post)

      /* TODO
        - one function that checks constraint
        - algorithm that approximated the constraint
      */
      // First try Z3 alone
      //val (res, model) = feelingLucky(constr, vc.allVariables)
      //constr.status = res
      //constr.model = model

      // If Z3 failed ...
      constr.status match {
        case (None | Some(DUNNO) | Some(NOT_SURE)) =>
          // ... try XFloat alone
          val constraint = constraintWithXFloat(constr, vc.inputs)
          val (resAA, modelAA) = feelingLucky(constraint, vc.allVariables)
          println("REEESULT: " + resAA)
        case _ =>;
      }

      // If neither work, do partial approx.

    }

    val totalTime = (System.currentTimeMillis - start)
    vc.verificationTime = Some(totalTime)
  }

  private def constraintWithXFloat(c: Constraint, inputs: Map[Variable, Record]): Constraint = {
    reporter.info("Now trying with XFloat only...")

    val solver = new NumericSolver(ctx, program)

    val paths = collectPaths(c.body).map(p => p.addCondition(filterPreconditionForBoundsIteration(c.pre)))
    //println("paths")
    //println(paths.mkString("\n"))

    for (path <- paths) {
      //println("Investigating path: " + path)

      // TODO: make sure we push the correct bounds, i.e. not real-valued when it
      // was supposed to be floats and vice - versa
      val (variables, indices) = variables2xfloats(inputs, solver, path.condition)

      val result = inXFloats(path.expression, variables, solver, path.condition)
      path.value = Some(result(ResultVariable()))
      //println("result: " + result)
    }

    // Merge results from all branches
    val (interval, error) = mergePaths(paths)
    println("max interval: " + interval)
    println("max error: " + error)

    // Create constraint
    val newBodyConstraint = createConstraintFromResults(Map(ResultVariable() -> (interval, error)))
    println("constraint: " + newBodyConstraint)
    Constraint(And(c.pre, newBodyConstraint), BooleanLiteral(true), c.post)

  }


  /*def checkConstraint(c: Constraint, allVars: Seq[Variable]): (Option[Valid], Option[Map[Identifier, Expr]]) = {
    // step 1: translate our own constructs into something Z3 will understand
    // i.e. AbsTransformer has to become a NoiseTransformer

    // step 2: generate constraint with buddies and roundoff errors




  }*/

  // no approximation
  def feelingLucky(c: Constraint, allVars: Seq[Variable]): (Option[Valid], Option[Map[Identifier, Expr]]) = {
    reporter.info("Now trying with Z3 only...")
    val toProve = exprToConstraint(allVars, c.pre, c.body, c.post, reporter)
    val constraint = absTransform.transform(toProve)
    if (verbose) println("\n expr before: " + toProve)
    if (verbose) println("\n expr after: " + constraint)

    val (valid, model) = solver.checkValid(constraint)
    (Some(valid), model)
  }

  def filterPreconditionForBoundsIteration(expr: Expr): Expr = expr match {
    case And(args) =>
      And(args.map(a => filterPreconditionForBoundsIteration(a)))
    case Noise(e, f) => BooleanLiteral(true)
    case Roundoff(e) => BooleanLiteral(true)
    case _ => expr
  }

  // Returns a map from all variables to their final value, including local vars
  def inXFloats(exprs: List[Expr], vars: Map[Expr, XFloat], solver: NumericSolver, pre: Expr): Map[Expr, XFloat] = {
    var currentVars: Map[Expr, XFloat] = vars

    for (expr <- exprs) expr match {
      case Equals(variable, value) =>
        currentVars = currentVars + (variable -> inXFloats(value, currentVars, solver, pre))

      case _ =>
        throw UnsupportedFragmentException("This shouldn't be here: " + expr.getClass + "  " + expr)
    }

    currentVars
  }

  // Evaluates an arithmetic expression
  def inXFloats(expr: Expr, vars: Map[Expr, XFloat], solver: NumericSolver, pre: Expr): XFloat = expr match {
    case v @ Variable(id) => vars(v)
    case RationalLiteral(v) => XFloat(v, solver, pre)
    case IntLiteral(v) => XFloat(v, solver, pre)
    case UMinus(rhs) => - inXFloats(rhs, vars, solver, pre)
    case Plus(lhs, rhs) => inXFloats(lhs, vars, solver, pre) + inXFloats(rhs, vars, solver, pre)
    case Minus(lhs, rhs) => inXFloats(lhs, vars, solver, pre) - inXFloats(rhs, vars, solver, pre)
    case Times(lhs, rhs) => inXFloats(lhs, vars, solver, pre) * inXFloats(rhs, vars, solver, pre)
    case Division(lhs, rhs) => inXFloats(lhs, vars, solver, pre) / inXFloats(rhs, vars, solver, pre)
    case _ =>
      throw UnsupportedFragmentException("Can't handle: " + expr.getClass)
      null
  }

  def createConstraintFromResults(results: Map[Expr, (RationalInterval, Rational)]): Expr = {
    var args: Seq[Expr] = Seq.empty
    for((v, (interval, error)) <- results) {

      args = args :+ LessEquals(RationalLiteral(interval.xlo), v)
      args = args :+ LessEquals(v, RationalLiteral(interval.xhi))
      args = args :+ Noise(v, RationalLiteral(error))
    }
    And(args)
  }



  private def mergePaths(paths: Set[Path]): (RationalInterval, Rational) = {
    import Rational._
    var interval = paths.head.value.get.interval
    var error = paths.head.value.get.maxError

    for (path <- paths.tail) {
      interval = RationalInterval(min(interval.xlo, path.value.get.interval.xlo),
                                  max(interval.xhi, path.value.get.interval.xhi))
      error = max(error, path.value.get.maxError)
    }
    (interval, error)
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


  /*
    Translates the Abs(x) tree node into two inequalities.
  */
  class AbsTransformer extends TransformerWithPC {
    type C = Seq[Expr]
    val initC = Nil

    def register(e: Expr, path: C) = path :+ e

    override def rec(e: Expr, path: C) = e match {
      case LessEquals(Abs(expr), r @ RationalLiteral(value)) =>
        And(LessEquals(RationalLiteral(-value), expr),
          LessEquals(expr, r))
      case LessThan(Abs(expr), r @ RationalLiteral(value)) =>
        And(LessThan(RationalLiteral(-value), expr),
          LessThan(expr, r))
      case GreaterEquals(r @ RationalLiteral(value), Abs(expr)) =>
        And(LessEquals(RationalLiteral(-value), expr),
          LessEquals(expr, r))
      case GreaterThan(r @ RationalLiteral(value), Abs(expr)) =>
        And(LessThan(RationalLiteral(-value), expr),
          LessThan(expr, r))
      case _ =>
        super.rec(e, path)
    }

  }
}
