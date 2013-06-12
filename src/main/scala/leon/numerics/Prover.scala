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
          val constraint = constraintWithXFloat(c, vc.inputs)
          val (resAA, modelAA) = checkConstraint(constraint, vc.allVariables)
          println("XFloat only result: " + resAA)
          c.status = resAA
          c.model = modelAA
        case _ =>;
      }

      // If neither work, do partial approx.

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

    val body = And(Or(realPart), Or(noisyPart))
    val toCheck = Implies(And(precondition, body), postcondition)

    //println("toCheck: " + toCheck)
    if (reporter.errorCount == 0) {
      val (valid, model) = solver.checkValid(toCheck)
      (Some(valid), model)
    } else {
      (None, None)
    }

  }

  // TODO: approximatePath

  private def constraintWithXFloat(c: Constraint, inputs: Map[Variable, Record]): Constraint = {
    reporter.info("Now trying with XFloat only...")

    //val solver = new NumericSolver(ctx, program)

    val paths = c.paths.map(p => p.addCondition(filterPreconditionForBoundsIteration(c.pre)))
    //println("paths")
    //println(paths.mkString("\n"))

    for (path <- paths) {
      //println("Investigating path: " + path)

      // TODO: make sure we push the correct bounds, i.e. not real-valued when it
      // was supposed to be floats and vice - versa
      val (variables, indices) = variables2xfloats(inputs, solver, path.condition)

      val result: Map[Expr, XFloat] = inXFloats(path.expression, variables, solver, path.condition)
      println("path result: " + result)
      path.values = result
    }

    // Merge results from all branches
    val (interval, error) = mergePathResults(paths)(ResultVariable())
    /*val (interval, error) = mergeResultForKey(paths, ResultVariable())
    println("max interval: " + interval)
    println("max error: " + error)
    */
    // Create constraint
    val newBodyConstraint = createConstraintFromResults(Map(ResultVariable() -> (interval, error)))
    println("constraint: " + newBodyConstraint)
    Constraint(And(c.pre, newBodyConstraint), BooleanLiteral(true), c.post)

  }


  private def getVariables(variables: Seq[Variable]): (Variable, Variable, Map[Expr, Expr]) = {
    val resVar = Variable(FreshIdentifier("res")).setType(RealType)
    val machineEps = Variable(FreshIdentifier("#eps")).setType(RealType)

    var buddies: Map[Expr, Expr] =
      variables.foldLeft(Map[Expr, Expr](resVar -> Variable(FreshIdentifier("#res_0")).setType(RealType)))(
        (map, nextVar) => map + (nextVar -> Variable(FreshIdentifier("#"+nextVar.id.name+"_0")).setType(RealType))
      )

    (resVar, machineEps, buddies)
  }


  private def filterPreconditionForBoundsIteration(expr: Expr): Expr = expr match {
    case And(args) =>
      And(args.map(a => filterPreconditionForBoundsIteration(a)))
    case Noise(e, f) => BooleanLiteral(true)
    case Roundoff(e) => BooleanLiteral(true)
    case _ => expr
  }

  // Returns a map from all variables to their final value, including local vars
  private def inXFloats(exprs: List[Expr], vars: Map[Expr, XFloat], solver: NumericSolver, pre: Expr): Map[Expr, XFloat] = {
    var currentVars: Map[Expr, XFloat] = vars

    for (expr <- exprs) expr match {
      case Equals(variable, value) =>
        currentVars = currentVars + (variable -> inXFloats(value, currentVars, solver, pre))

      case _ =>
        reporter.error("AA cannot handle: " + expr)
        //throw UnsupportedFragmentException("This shouldn't be here: " + expr.getClass + "  " + expr)
    }

    currentVars
  }

  // Evaluates an arithmetic expression
  private def inXFloats(expr: Expr, vars: Map[Expr, XFloat], solver: NumericSolver, pre: Expr): XFloat = expr match {
    case v @ Variable(id) => vars(v)
    case RationalLiteral(v) => XFloat(v, solver, pre)
    case IntLiteral(v) => XFloat(v, solver, pre)
    case UMinus(rhs) => - inXFloats(rhs, vars, solver, pre)
    case Plus(lhs, rhs) => inXFloats(lhs, vars, solver, pre) + inXFloats(rhs, vars, solver, pre)
    case Minus(lhs, rhs) => inXFloats(lhs, vars, solver, pre) - inXFloats(rhs, vars, solver, pre)
    case Times(lhs, rhs) => inXFloats(lhs, vars, solver, pre) * inXFloats(rhs, vars, solver, pre)
    case Division(lhs, rhs) => inXFloats(lhs, vars, solver, pre) / inXFloats(rhs, vars, solver, pre)
    case Sqrt(t) => inXFloats(t, vars, solver, pre).squareRoot
    case _ =>
      reporter.error("AA cannot handle: " + expr)
      //throw UnsupportedFragmentException("Can't handle: " + expr.getClass)
      XFloat(Rational(0), solver, BooleanLiteral(true))
  }

  private def createConstraintFromResults(results: Map[Expr, (RationalInterval, Rational)]): Expr = {
    var args: Seq[Expr] = Seq.empty
    for((v, (interval, error)) <- results) {

      args = args :+ LessEquals(RationalLiteral(interval.xlo), v)
      args = args :+ LessEquals(v, RationalLiteral(interval.xhi))
      args = args :+ Noise(v, RationalLiteral(error))
    }
    And(args)
  }



  private def mergePathResults(paths: Set[Path]): Map[Expr, (RationalInterval, Rational)] = {
    import Rational._

    println("---------------")

    var collection: Map[Expr, List[XFloat]] = Map.empty
    for (path <- paths) {
      for ((k, v) <- path.values) {
        collection = collection + ((k, List(v) ++ collection.getOrElse(k, List())))
      }
    }
    println("collection: " + collection)

    var resMap: Map[Expr, (RationalInterval, Rational)] = Map.empty
    for ((k, list) <- collection) {
      var lo = list.head.interval.xlo
      var hi = list.head.interval.xhi
      var err = list.head.maxError

      for (xf <- list.tail) {
        lo = min(lo, xf.interval.xlo)
        hi = max(hi, xf.interval.xhi)
        err = max(err, xf.maxError)
      }
      resMap = resMap + ((k, (RationalInterval(lo, hi), err)))
    }

    /*val keys: Set[Expr] = paths.collect {
      case p => p.values.keys.toSet
    }

    val resMap: Map[Expr, (RationalInterval, Rational)] = Map.empty

    for (key <- keys) {
      var interval 

    }
    var interval = paths.head.values(key).interval
    var error = paths.head.values(key).maxError

    for (path <- paths.tail) {
      interval = RationalInterval(min(interval.xlo, path.values(key).interval.xlo),
                                  max(interval.xhi, path.values(key).interval.xhi))
      error = max(error, path.value.get.maxError)
    }
    (interval, error)
    */
    println("\nresMap: " + resMap)
    resMap
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


}
