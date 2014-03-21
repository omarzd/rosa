/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import purescala.Common._
import purescala.Trees._
import purescala.Definitions._
import purescala.TreeOps._
import purescala.TypeTrees.{Int32Type, RealType, TupleType}

import real.Trees.{Noise, Roundoff, Actual, UpdateFunction, Iteration, RealLiteral, FncValue, FncBody}
import real.TreeOps._
import Rational._
import Calculus._

case class Approximations(options: RealOptions, fncs: Map[FunDef, Fnc], reporter: Reporter, solver: RangeSolver,
  vc: VerificationCondition) {
  import Approximations._
  import FncHandling._
  import ArithmApprox._
  import PathHandling._

  implicit val debugSection = utils.DebugSectionReals

  //var kinds: List[ApproxKind] = List.empty
  val containsIfs = containsIfExpr(vc.body)
  val containsFncs = vc.allFncCalls.nonEmpty
  
  //println("initializing " + vc)
  //println(vc.recursive)

  var kinds = allApprox

  if (vc.kind == VCKind.LoopPost) kinds = kinds.filter(_.arithmApprox == NoApprox)
  else if (!options.z3Only) kinds = kinds.filter(_.arithmApprox != NoApprox)

  //println("after z3Only: " + kinds)

  if (!containsIfs || options.pathError) kinds = kinds.filter(_.pathHandling == Merging)
  //println("after ifs: " + kinds)

  if (!containsFncs) kinds = kinds.filter(_.fncHandling == Uninterpreted)
  else kinds = kinds.filter(_.fncHandling != Uninterpreted)
  //println("after fnc: " + kinds)

  if (vc.kind == VCKind.LoopPost) kinds = kinds.filter(ak => ak.fncHandling == Postcondition && ak.pathHandling == Pathwise)
  //println("kinds: " + kinds)

  /*
    Computing sigma (roundoff error, strating with exact inputs) and
    K, Lipschitz constant, of a potentially multivariate function.
    @param ids function variables 
  */
  def getSigmaK(precondition: Expr, expr: Expr, exprf: Expr, ids: Seq[Identifier], precision: Precision): (Rational, Rational) = {
    val transformer = new Approximator(reporter, solver, precision, vc.pre, vc.variables, false, true)
    val sigma = transformer.computeError(exprf)

    reporter.debug("\u03C3: " + sigma)
    val k = maxAbs(ids.flatMap { x =>
      val exprPrime = d(expr, x)
      val rangeDerivative = solver.getRange(precondition, exprPrime, vc.variables,
                solverMaxIterMedium, solverPrecisionMedium) 
      reporter.debug("Lipschitz constants wrt " + x + ": " + rangeDerivative.xlo +
                      ", " + rangeDerivative.xhi)
      Seq(rangeDerivative.xlo, rangeDerivative.xhi)
      })
    reporter.debug("k: " + k)
    (sigma, k)
  }

  def getSigmaKMap(precondition: Expr, expr: Expr, exprf: Expr, ids: Seq[Identifier], precision: Precision): 
    (Rational, Map[Identifier, Rational]) = {
    val transformer = new Approximator(reporter, solver, precision, vc.pre, vc.variables, false, true)
    val sigma = transformer.computeError(exprf)

    reporter.debug("\u03C3: " + sigma)
    val kMap = ids.map { x =>
      val exprPrime = d(expr, x)
      val rangeDerivative = solver.getRange(precondition, exprPrime, vc.variables,
                  solverMaxIterMedium, solverPrecisionMedium) 
      reporter.debug("Lipschitz constants wrt " + x + ": " + rangeDerivative.xlo +
                      ", " + rangeDerivative.xhi)
      //println("Lipschitz constants wrt " + x + ": " + rangeDerivative.xlo +
      //                ", " + rangeDerivative.xhi)
      (x, maxAbs(Seq(rangeDerivative.xlo, rangeDerivative.xhi)))
      }.toMap
    reporter.debug("ks: " + kMap)
    (sigma, kMap)
  }

  def getLoopErrorInfinityNorm(preReal: Expr, expr: Expr, exprFinite: Expr, ids: Seq[Identifier],
    precision: Precision): (Rational, Rational, Option[Rational]) = {
    val (sigma, k) = getSigmaK(preReal, expr, exprFinite, ids, precision)
            
    vc.funDef.loopBound match {
      case Some(n) =>
        val initErrors = getInitialErrors(vc.variables, precision)
        val totalError = errorFromNIterations(n, maxAbs(initErrors.values.toSeq), sigma, k)
        (sigma, k, Some(totalError))
      case _ => 
        (sigma, k, None)
    }
  }

  /*def getLoopErrorComponentWise(preReal: Expr, expr: Expr, exprFinite: Expr,
    ids: Seq[Identifier]): (Rational, Rational, Option[Rational]) = {
    val (sigma, kMap) = getSigmaKMap(preReal, expr, exprFinite, ids)
            
    vc.funDef.loopBound match {
      case Some(n) =>
        val initErrors = getInitialErrors(vc.variables, precision)

        // TODO: we have to do this for all update functions simultaneously

        val totalError = errorFromNIterations(n, maxAbs(initErrors.values.toSeq), sigma, k)   
        (sigma, k, Some(totalError))
      case _ =>
        (sigma, k, None)
    }
  }*/

  def getErrorWithLipschitzInfinityNorm(preReal: Expr, path: Path, precision: Precision): Option[Rational] = {
    // check whether we can apply this
    // no ifs and no tuples (for now)
    if (containsIfExpr(path.bodyReal) || containsFunctionCalls(path.bodyReal) || vc.variables.resIds.length > 1) {
      None
    } else {
      val ids = vc.variables.inputs.keys.map(k => k.asInstanceOf[Variable].id).toSeq
      reporter.debug("ids: " + ids)
      // TODO: removing errors here is not sound, we need total ranges, including errors
      val (sigma, k) = getSigmaK(preReal, inlineBody(path.bodyReal), path.bodyFinite, ids, precision)
      val initErrors = getInitialErrors(vc.variables, precision)
      reporter.debug("initial errors: " + initErrors)
      val totalError = k * maxAbs(initErrors.values.toSeq) + sigma
      reporter.info(s"($sigma, $k), total error: " + totalError)
      Some(totalError)
    }  
  }

  def getErrorWithLipschitzComponentWise(preReal: Expr, path: Path, precision: Precision): Option[Rational] = {
    // check whether we can apply this
    // no ifs and no tuples (for now)
    if (containsIfExpr(path.bodyReal) || containsFunctionCalls(path.bodyReal) || vc.variables.resIds.length > 1) {
      None
    } else {
      val ids = vc.variables.inputs.keys.map(k => k.asInstanceOf[Variable].id).toSeq
      reporter.debug("ids: " + ids)
      // TODO: removing errors here is not sound, we need total ranges, including errors
      val (sigma, kMap) = getSigmaKMap(preReal, inlineBody(path.bodyReal), path.bodyFinite, ids, precision)
      val initErrors = getInitialErrors(vc.variables, precision)

      val rowSum = kMap.foldLeft(zero){
        case (sum, (id, k)) => 
          //println(id + ", k: " + k + ", init error: " + initErrors(id) + ", contrib.: " + k*initErrors(id))
          sum + k*initErrors(id) 
      }
      reporter.debug("initial errors: " + initErrors)
      val totalError = rowSum + sigma
      //val totalError = k * maxAbs(initErrors.values.toSeq) + sigma
      reporter.info(s"($sigma, " + kMap.values.mkString(";") + "), total error (componentwise): " + totalError)
      Some(totalError)
    }  
  }

  /*
    Get approximation for results of an expression.
  */
  def getApproximationAndSpec_ResultOnly(path: Path, precision: Precision): (Expr, Seq[Spec]) = path.bodyFinite match {
    //case True => (True, Seq())
    case body =>
      val approximator = new Approximator(reporter, solver, precision, And(vc.pre, path.condition),
                                                vc.variables, options.pathError)
      val approx = approximator.getXRealForResult(body)
      val zipped = vc.variables.fResultVars.zip(approx)

      val specs = zipped.map({
        case (fresVar: Variable, resXFloat: XReal) =>
          Spec(fresVar.id, RationalInterval(resXFloat.realInterval.xlo, resXFloat.realInterval.xhi), Some(resXFloat.maxError))
        })

      val constraint = And(zipped.foldLeft(Seq[Expr]())(
        (seq, kv) => seq ++ Seq(LessEquals(RealLiteral(kv._2.interval.xlo), kv._1),
                                LessEquals(kv._1, RealLiteral(kv._2.interval.xhi)),
                                Noise(vc.variables.getIdeal(kv._1), RealLiteral(kv._2.maxError)))))
      (constraint, specs)
    }

 /*
    Get approximation for results and all intermediate variables.
    Used for proving preconditions.
  */
  def getApproximationAndSpec_AllVars(path: Path, precision: Precision): Expr = path.bodyFinite match {
    case True => True // noop
    case body => 
      val approximator = new Approximator(reporter, solver, precision, And(vc.pre, path.condition),
                                                  vc.variables, options.pathError)
      val approxs: Map[Expr, XReal] = approximator.getXRealForAllVars(body)
      
      val constraint = And(approxs.foldLeft(Seq[Expr]())(
          (seq, kv) => seq ++ Seq(LessEquals(RealLiteral(kv._2.interval.xlo), kv._1),
                                  LessEquals(kv._1, RealLiteral(kv._2.interval.xhi)),
                                  Noise(vc.variables.getIdeal(kv._1), RealLiteral(kv._2.maxError)))))
      constraint
  }

  // Note: only supports function calls in fnc bodies, not in pre and post
  def getApproximation(kind: ApproxKind, precision: Precision, postMap: Map[FunDef, Seq[Spec]]): Approximation = {
    reporter.debug("getting approximation: " + kind)
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
  
    val precondition = vc.pre
    val preReal = removeErrors(precondition)
    val postcondition = vc.post

    /* --------------  Functions -------------- */
    var body = kind.fncHandling match {
      case Uninterpreted => vc.body
      case Postcondition => inlinePostcondition(vc.body, precision, postMap)
      case Inlining => inlineFunctions(vc.body, fncs)
    }
    if (kind.fncHandling != Uninterpreted)
      reporter.debug("after FNC handling:\npre: %s\nbody: %s\npost: %s".format(precondition,body,postcondition))

    /* -------------- If-then-else -------------- */
    val paths: Set[Path] = (vc.kind, kind.pathHandling) match {
      case (VCKind.LoopPost, _) => body match {
        case IfExpr(c, thenn, elze) if (validLoopCondition(c)) =>
          val thennClean = thenn//removeLoopCounterUpdate(thenn)
          val elzeClean = elze//removeLoopCounterUpdate(elze)

          Set(Path(True, filterOutActualInFncVal(thennClean), idealToActual(thennClean, vc.variables)),
            Path(True, filterOutActualInFncVal(elzeClean), idealToActual(elzeClean, vc.variables)))
          //Set(Path(True, thennClean, True), Path(True, elzeClean, True))

        case _ =>
          println(body.getClass)
          reporter.error("Unsupported loop type.")
          Set()
      }     

      case (_, Pathwise) => getPaths(body).map {
        case (cond, expr) => Path(cond, filterOutActualInFncVal(expr), idealToActual(expr, vc.variables))
      }
      case (VCKind.LoopInvariant, Merging) =>
        val bodyClean = removeLoopCounterUpdate(body)
        Set(Path(True, filterOutActualInFncVal(bodyClean), idealToActual(bodyClean, vc.variables)))

      case (_, Merging) =>  Set(Path(True, filterOutActualInFncVal(body), idealToActual(body, vc.variables)))
    }
    reporter.debug("after PATH handling:\nbody: %s".format(paths.mkString("\n")))

    if (vc.isLoop) {
      reporter.debug("vc is a loop")
      var constraints = Seq[Constraint]()

      body match {
        case Iteration(ids, body, updateFncs) =>
          val inlinedUpdateFns = inlineBody(body, updateFncs.asInstanceOf[Seq[UpdateFunction]])
          reporter.debug("inlined fncs: " + inlinedUpdateFns)

          // List[(maxError, max Lipschitz constant, max loop error)]
          val errors: Seq[(Rational, Rational, Option[Rational])] = inlinedUpdateFns.map({
            case UpdateFunction(v, expr) =>
              reporter.debug("")
              reporter.debug("real update fnc for " + v + ": " + expr)
              // TODO: this has already been done before (with path handling)
              val exprFinite = idealToActual(expr, vc.variables)
              reporter.debug("finite expr: " + exprFinite)

              val (sigma, k, err) = getLoopErrorInfinityNorm(preReal, expr, exprFinite, ids, precision)
              reporter.info(s"$v: (sigma: $sigma, k: $k), total error: " + err)
              (sigma, k, err)
          })
        case _ => reporter.error("cannot handle anything but a simple loop for now...")
      }

      Approximation(kind, constraints, emptySpecTuple)
    } else {
      kind.arithmApprox match {
        case NoApprox =>
          var constraints = Seq[Constraint]()
          for (path <- paths) {
            constraints :+= Constraint(And(precondition, path.condition), path.bodyReal, path.bodyFinite, postcondition)
          }
          Approximation(kind, constraints, Seq())
          
        case JustFloat =>
          var constraints = Seq[Constraint]()
          var specsPerPath = Seq[SpecTuple]()
          var spec: SpecTuple = Seq() // seq since we can have tuples

          for ( path <- paths if (isFeasible(And(precondition, path.condition))) ) {
            //solver.clearCounts          
            if (vc.kind == VCKind.Precondition || vc.kind == VCKind.LoopInvariant) {
              val bodyApprox = getApproximationAndSpec_AllVars(path, precision)
              reporter.debug("body approx: " + bodyApprox)    
              constraints :+= Constraint(And(precondition, path.condition), path.bodyReal, bodyApprox,
                postcondition)
            } else {
              /*val lipschitzErrorInf = getErrorWithLipschitzInfinityNorm(preReal, path)
              reporter.info("lipschitzError (infinity norm): \n" + lipschitzErrorInf)

              val lipschitzErrorComp = getErrorWithLipschitzComponentWise(preReal, path)
              reporter.info("lipschitzError (component-wise): \n" + lipschitzErrorComp)
              */
              val (bodyApprox, nextSpecs) = getApproximationAndSpec_ResultOnly(path, precision)
              spec = mergeSpecs(spec, nextSpecs) //TODO do at the end?
              specsPerPath :+= nextSpecs
              constraints :+= Constraint(And(precondition, path.condition), path.bodyReal, bodyApprox, postcondition)
              reporter.debug("body approx: " + bodyApprox)    
            }
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
                  Constraint(cnstr.precondition, And(specs.map(_.toRealExpr)), cnstr.finiteComp, cnstr.postcondition)
              Approximation(kind, newConstraints, approx.spec)
            case None =>
              throw new RealArithmeticException("Cannot compute Float'n'Range approximation because JustFloat approximation is missing.")
              null
          }
      }
    }
  }

  private def removeLoopCounterUpdate(e: Expr): Expr = {
    preMap {
      case Equals(tmp, Plus(c, IntLiteral(1))) => Some(True)
      case Equals(tmp, Minus(c, IntLiteral(1))) => Some(True)
      case LessEquals(l, r) if (l.getType == Int32Type && r.getType == Int32Type) => Some(True)
      case LessThan(l, r) if (l.getType == Int32Type && r.getType == Int32Type) => Some(True)
      case GreaterEquals(l, r) if (l.getType == Int32Type && r.getType == Int32Type) => Some(True)
      case GreaterThan(l, r) if (l.getType == Int32Type && r.getType == Int32Type) => Some(True)
      case _ => None
    }(e)
  }


  private def validLoopCondition(e: Expr) = e match {
    case LessEquals(l, r) =>
      println(l.getType + "  " + r.getType)
      (l.getType == Int32Type && r.getType == Int32Type)
    case LessThan(l, r) => 
    println(l.getType + "  " + r.getType)
    (l.getType == Int32Type && r.getType == Int32Type)
    case GreaterEquals(l, r) =>
      println(l.getType + "  " + r.getType)
       (l.getType == Int32Type && r.getType == Int32Type)
    case GreaterThan(l, r) => 
      println(l.getType + "  " + r.getType)
      (l.getType == Int32Type && r.getType == Int32Type)
    case _ =>
      println("other")
      false
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

  private def inlineBody(body: Expr): Expr = {
    var valMap: Map[Expr, Expr] = Map.empty
    val lastInstruction = preMap { expr => expr match {
        case Equals(v @ Variable(id), rhs) =>
          valMap = valMap + (v -> replace(valMap,rhs))
          Some(True)
        case x => Some(x)  //last instruction
      }
    }(body)
    //println("last instruction: " + lastInstruction)
    val res = replace(valMap, lastInstruction)
    //println("res: " + res)
    res
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

  def extractSpecs(e: Expr, id: Identifier): Option[Spec] = {
    var lwrBoundReal: Option[Rational] = None
    var upBoundReal: Option[Rational] = None
    var lwrBoundActual: Option[Rational] = None
    var upBoundActual: Option[Rational] = None
    var error: Option[Rational] = None
    var extras = List[Expr]()

    preTraversal{
      case LessEquals(RealLiteral(lwrBnd), Variable(id)) => lwrBoundReal = Some(lwrBnd)
      case LessEquals(Variable(id), RealLiteral(uprBnd)) => upBoundReal = Some(uprBnd)
      case LessThan(RealLiteral(lwrBnd), Variable(id)) => lwrBoundReal = Some(lwrBnd)
      case LessThan(Variable(id), RealLiteral(uprBnd)) =>  upBoundReal = Some(uprBnd)
      case GreaterEquals(RealLiteral(uprBnd), Variable(id)) =>  upBoundReal = Some(uprBnd)
      case GreaterEquals(Variable(id), RealLiteral(lwrBnd)) => lwrBoundReal = Some(lwrBnd)
      case GreaterThan(RealLiteral(uprBnd), Variable(id)) =>  upBoundReal = Some(uprBnd)
      case GreaterThan(Variable(id), RealLiteral(lwrBnd)) => lwrBoundReal = Some(lwrBnd)

      case LessEquals(RealLiteral(lwrBnd), Actual(Variable(id))) => lwrBoundActual = Some(lwrBnd)
      case LessEquals(Actual(Variable(id)), RealLiteral(uprBnd)) => upBoundActual = Some(uprBnd)
      case LessThan(RealLiteral(lwrBnd), Actual(Variable(id))) => lwrBoundActual = Some(lwrBnd)
      case LessThan(Actual(Variable(id)), RealLiteral(uprBnd)) => upBoundActual = Some(uprBnd)
      case GreaterEquals(RealLiteral(uprBnd), Actual(Variable(id))) => upBoundActual = Some(uprBnd)
      case GreaterEquals(Actual(Variable(id)), RealLiteral(lwrBnd)) => lwrBoundActual = Some(lwrBnd)
      case GreaterThan(RealLiteral(uprBnd), Actual(Variable(id))) => upBoundActual = Some(uprBnd)
      case GreaterThan(Actual(Variable(id)), RealLiteral(lwrBnd)) => lwrBoundActual = Some(lwrBnd)

      case Noise(Variable(id), RealLiteral(value)) => error = Some(value)

      case Times(_, _) | Plus(_, _) | Division(_, _) | Minus(_, _) | UMinus(_) =>
        println("found integer")
        throw new Exception("found integer arithmetic in ResultCollector")

      case _ => ;
    } (e)


    // TODO: for loops the error won't be given, we need to extract this anyway somehow
    
    error match {
      case Some(err) =>
        if ((lwrBoundReal.nonEmpty || lwrBoundActual.nonEmpty) && (upBoundReal.nonEmpty || upBoundActual.nonEmpty)) {
          Some(Spec(id, RationalInterval(lwrBoundReal.getOrElse(lwrBoundActual.get - err),
             upBoundReal.getOrElse(upBoundActual.get + err)), error))
        } else {
          None
        }
        // if we don't have the error, we cannot convert the actual range into a real one
      case None => 
        if (lwrBoundReal.nonEmpty && upBoundReal.nonEmpty) {
          Some(Spec(id, RationalInterval(lwrBoundReal.get, upBoundReal.get), None))
        } else {
          None
        }
    }
    /*
    //error flatMap ( err => {
    if ((lwrBoundReal.nonEmpty || lwrBoundActual.nonEmpty) && (upBoundReal.nonEmpty || upBoundActual.nonEmpty)) {
       Some(Spec(id, RationalInterval(lwrBoundReal.getOrElse(lwrBoundActual.get - err),
             upBoundReal.getOrElse(upBoundActual.get + err)), error))
    } else {
      None
    }
    })*/
  }


  def inlineFunctions(e: Expr, fncs: Map[FunDef, Fnc]): Expr = {
    preMap {
      case FunctionInvocation(funDef, args) =>
        val arguments: Map[Expr, Expr] = funDef.fd.params.map(decl => decl.toVariable).zip(args).toMap
        val fncBody = fncs(funDef.fd).body

        val newBody = replace(arguments, fncBody)
        Some(FncBody(funDef.id.name, newBody, funDef.fd, args))

      case _ =>  None
    }(e)
  }

  /*
    Replace the function call with its specification. For translation to Z3 FncValue needs to be translated
    with a fresh variable. For approximation, translate the spec into an XFloat.
  */
  def inlinePostcondition(expr: Expr, precision: Precision, postcondMap: Map[FunDef, Seq[Spec]]): Expr = {
    def actualToRealSpec(e: Expr, deltas: Map[Identifier, Rational]): Expr = {
      val ids = deltas.keys.toSeq

      // this is replacing the actuals, we will probably want to keep
      // either both, or what was given, maybe the latter would be better...
      postMap {
        case e @ LessEquals(RealLiteral(lwrBnd), Actual(Variable(id))) if (ids.contains(id)) =>
          Some(And(e, LessEquals(RealLiteral(lwrBnd - deltas(id)), Variable(id))))

        case e @ LessEquals(Actual(Variable(id)), RealLiteral(uprBnd)) if (ids.contains(id)) =>
          Some(And(e, LessEquals(Variable(id), RealLiteral(uprBnd + deltas(id)))))

        case e @ LessThan(RealLiteral(lwrBnd), Actual(Variable(id))) if (ids.contains(id)) =>
          Some(And(e, LessThan(RealLiteral(lwrBnd - deltas(id)), Variable(id))))

        case e @ LessThan(Actual(Variable(id)), RealLiteral(uprBnd)) if (ids.contains(id)) =>
          Some(And(e, LessThan(Variable(id), RealLiteral(uprBnd + deltas(id)))))

        case e @ GreaterEquals(RealLiteral(uprBnd), Actual(Variable(id))) if (ids.contains(id)) =>
          Some(And(e, GreaterEquals(RealLiteral(uprBnd + deltas(id)), Variable(id))))

        case e @ GreaterEquals(Actual(Variable(id)), RealLiteral(lwrBnd)) if (ids.contains(id)) =>
          Some(And(e, GreaterEquals(Variable(id), RealLiteral(lwrBnd - deltas(id)))))

        case e @ GreaterThan(RealLiteral(uprBnd), Actual(Variable(id))) if (ids.contains(id)) =>
          Some(And(e, GreaterThan(RealLiteral(uprBnd + deltas(id)), Variable(id))))

        case e @ GreaterThan(Actual(Variable(id)), RealLiteral(lwrBnd)) if (ids.contains(id)) =>
          Some(And(e, GreaterThan(Variable(id), RealLiteral(lwrBnd - deltas(id)))))

        case _ => None
      }(e)
    }

    var tmpCounter = 0

    def getFresh: Identifier = {
      tmpCounter = tmpCounter + 1
      FreshIdentifier("#tmp" + tmpCounter).setType(RealType)
    }

    preMap {
      case FunctionInvocation(typedFunDef, args) =>
        val funDef = typedFunDef.fd
        val arguments: Map[Expr, Expr] = funDef.params.map(decl => decl.toVariable).zip(args).toMap
        funDef.postcondition.flatMap({
          case (resId, postExpr) =>
            val resFresh = resId.getType match {
              case TupleType(bases) => Seq(getFresh, getFresh)
              case _ => Seq(getFresh)
            }
            //println(s"$resFresh")
            val postcondition = extractPostCondition(resId, postExpr, resFresh)
            //println(s"extracted: $postcondition")

            try {
              val specs: Seq[Spec] = resFresh.map( r => { extractSpecs(postcondition, r).get })
              //println("specs: " + specs)

              val deltaMap: Map[Identifier, Rational] =
                specs.filter(s => s.absError.nonEmpty).map( s => (s.id, s.absError.get)).toMap
              //println("deltaMap: " + deltaMap)
              val realSpecExpr = actualToRealSpec(postcondition, deltaMap)
              //println("realSpecExpr: " + realSpecExpr)

              Some(FncValue(specs, realSpecExpr))
            } catch {
              case e: Exception =>
                //Some(FncValue(Seq.empty, replace(arguments, postcondition)))
                None
            }
        }) match {
          case Some(fncValue) => Some(fncValue)
          case _ => postcondMap.getOrElse(funDef, Seq()) match {
            case specs: Seq[Spec] if specs.nonEmpty =>
              val specsExpr = And(specs.map(_.toExpr))
              Some(FncValue(specs, replace(arguments, specsExpr)))
            case _ =>
              throw PostconditionInliningFailedException("missing postcondition for " + funDef.id.name);
              null
          }
        }

      case _ => None
    }(expr)
  }

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
          val err = max(s1.absError.get, s2.absError.get)
          assert(s1.id == s2.id)
          Spec(s1.id, RationalInterval(lowerBnd, upperBnd), Some(err))
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
    val NoApprox = Value("NoApprox")
    val JustFloat = Value("JustFloat") // evaluate the float. part with xfloat
    val FloatNRange = Value("Float'n'Range") // also replace the real with an approx. of the range
  }
  import ArithmApprox._

  case class ApproxKind(fncHandling: FncHandling.Value, pathHandling: PathHandling.Value, arithmApprox: ArithmApprox.Value) {
    val allowsRealModel = (fncHandling == Uninterpreted && arithmApprox == JustFloat) || // no functions
                          (fncHandling == Inlining && arithmApprox == JustFloat) || // with fncs
                          (fncHandling == Inlining && arithmApprox == NoApprox) // with fncs
  }

  /*val a_FncIf = List(
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
  */

  // approximations are tried in this order
  val allApprox = List(
    ApproxKind(Uninterpreted, Merging, NoApprox),
    ApproxKind(Uninterpreted, Merging, JustFloat),
    ApproxKind(Uninterpreted, Merging, FloatNRange),
    ApproxKind(Uninterpreted, Pathwise, NoApprox),
    ApproxKind(Uninterpreted, Pathwise, JustFloat),
    ApproxKind(Uninterpreted, Pathwise, FloatNRange),

    ApproxKind(Postcondition, Merging, NoApprox),
    ApproxKind(Postcondition, Merging, JustFloat),
    ApproxKind(Postcondition, Merging, FloatNRange),
    ApproxKind(Postcondition, Pathwise, NoApprox),
    ApproxKind(Postcondition, Pathwise, JustFloat),
    ApproxKind(Postcondition, Pathwise, FloatNRange),

    ApproxKind(Inlining, Merging, NoApprox),
    ApproxKind(Inlining, Merging, JustFloat),
    ApproxKind(Inlining, Merging, FloatNRange),
    ApproxKind(Inlining, Pathwise, NoApprox),
    ApproxKind(Inlining, Pathwise, JustFloat),
    ApproxKind(Inlining, Pathwise, FloatNRange)
    )
  

}
