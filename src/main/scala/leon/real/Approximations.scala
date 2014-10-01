/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import purescala.Common._
import purescala.Trees._
import purescala.Definitions._
import purescala.TreeOps._
import purescala.TypeTrees.{Int32Type, RealType, TupleType, LoopCounterType}

import real.Trees._
import real.TreeOps._
import Rational._
//import Calculus._
import VariableShop._
import Precision._
import Spec._

case class Approximations(options: RealOptions, fncs: Map[FunDef, Fnc], val reporter: Reporter, val solver: RangeSolver,
  vc: VerificationCondition) extends Lipschitz {
  import Approximations._
  import FncHandling._
  import ArithmApprox._
  import PathHandling._

  implicit override val debugSection = utils.DebugSectionApprox

  var leonToZ3: LeonToZ3Transformer = null
  
  val taylorError = false

  val containsIfs = containsIfExpr(vc.body)
  val containsFncs = vc.allFncCalls.nonEmpty
  val checkPathError = !vc.funDef.annotations.contains("robust")
  
  var kinds = allApprox

  if (vc.kind == VCKind.LoopPost) {
    kinds = kinds.filter(x => x.arithmApprox == NoApprox && x.fncHandling == Postcondition &&
       x.pathHandling == Pathwise)
  } else {
    //println("before: " + kinds)
    if (!options.z3Only) kinds = kinds.filter(_.arithmApprox != NoApprox)

    if (!containsIfs) {
      kinds = kinds.filter(_.pathHandling == Merging)
    } else if(options.lipschitzPathError && checkPathError) {
      kinds = kinds.filter(_.pathHandling == Pathwise)
    } else if(checkPathError) {
      kinds = kinds.filter(_.pathHandling == Merging)
    }
    
    if (!containsFncs) kinds = kinds.filter(_.fncHandling == Uninterpreted)
    else kinds = kinds.filter(_.fncHandling != Uninterpreted)
  }

  // Note: only supports function calls in fnc bodies, not in pre and post
  def getApproximation(kind: ApproxKind, precision: Precision, postMap: Map[FunDef, Seq[Spec]]): Approximation = {
    reporter.debug("getting approximation: " + kind)

    leonToZ3 = new LeonToZ3Transformer(vc.variables, precision)

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
    val preReal = removeErrorsAndActual(precondition)
    val postcondition = vc.post

    /* --------------  Functions -------------- */
    var body = kind.fncHandling match {
      case Uninterpreted => vc.body
      case Postcondition =>
        val tmp = inlinePostcondition(vc.body, precision, postMap)
        vc.inlinedBody = Some(tmp)
        tmp
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
          //println(body.getClass)
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

        // do not filter paths according to feasibility here
        // TODO: path error with tuples
        val lipschitzPathError: Rational =
          if (options.lipschitzPathError && checkPathError) {
            val res = getLipschitzPathError(paths.toSeq, precision)
            reporter.info("--> lipschitzPathError: " + res)
            res
          }    
          else zero
        

        for ( path <- paths if (isFeasible(And(precondition, path.condition))) ) {
          reporter.debug("Computing approximation for path ...")
          //solver.clearCounts          
          if (vc.kind == VCKind.Precondition) {
            val bodyApprox = getApproximationAndSpec_AllVars(path, precision)
            reporter.debug("body approx: " + bodyApprox)    
            constraints :+= Constraint(And(precondition, path.condition), path.bodyReal, bodyApprox,
              postcondition)

          } else if(vc.kind == VCKind.LoopInvariant) {
            val (bodyApprox, loopSpecs) = getApproximationAndSpec_LoopInv(path, precision, preReal)
            spec = loopSpecs

            reporter.debug("body approx: " + bodyApprox)    
            constraints :+= Constraint(And(precondition, path.condition), path.bodyReal, bodyApprox,
              postcondition)

          } else {
            
            val (bodyApprox, nextSpecs) = getApproximationAndSpec_ResultOnly(path, precision,
              lipschitzPathError, preReal)
            reporter.debug("body approx: " + bodyApprox)
            
            //println("specs: " + nextSpecs)
            spec = mergeSpecs(spec, nextSpecs) //TODO do at the end?
            //println("merged: " + spec)
            specsPerPath :+= nextSpecs
            constraints :+= Constraint(And(precondition, path.condition), path.bodyReal, bodyApprox, postcondition)
            
          }
        }

        // this is not clean, but loops currently do not support path errors
        if (lipschitzPathError != zero)
          spec = spec.map(s => s.asInstanceOf[SimpleSpec].addPathError(lipschitzPathError))


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
  
  /*
    Get approximation for results of an expression.
  */
  private def getApproximationAndSpec_ResultOnly(path: Path, precision: Precision, pathError: Rational, preReal: Expr):
    (Expr, Seq[Spec]) = path.bodyFinite match {
    case body =>
      solver.clearCounts
      //var start = System.currentTimeMillis
      //val approximator = new Approximator(reporter, solver, precision, And(vc.pre, path.condition),
      //                                          vc.variables, options.pathError)
      //val approx = approximator.getXRealForResult(body)
      //println("current: " + approx)
      //println((System.currentTimeMillis - start) + "ms")

      //start = System.currentTimeMillis
      val approximatorNew = new AAApproximator(reporter, solver, precision, checkPathError, options.lipschitz)
      val approx = approximatorNew.approximate(body, And(vc.pre, path.condition), vc.variables, exactInputs = false)
      //println("new:     " + approxNew)
      //println((System.currentTimeMillis - start) + "ms")

      reporter.info("solver counts: " + solver.getCounts)
      val zipped = vc.variables.resultVars.zip(approx)

      val specs = zipped.map({
        case (resVar: Variable, resXFloat: XReal) =>
          SimpleSpec(resVar.id, RationalInterval(resXFloat.realInterval.xlo, resXFloat.realInterval.xhi),
                    Some(resXFloat.maxError))
        })

      val constraint = And(zipped.foldLeft(Seq[Expr]())(
        (seq, kv) => seq ++ Seq(LessEquals(RealLiteral(kv._2.interval.xlo), vc.variables.buddy(kv._1)),
                                LessEquals(vc.variables.buddy(kv._1), RealLiteral(kv._2.interval.xhi)),
                                Noise(kv._1, RealLiteral( max(pathError, kv._2.maxError) )))))


      if (taylorError) {
        try {
          val ids = vc.variables.inputs.keys.map(k => k.asInstanceOf[Variable].id).toSeq
          val initErrors = vc.variables.getInitialErrors(precision)

          val vars = vc.variables.getInitIntervals(precision)
          //val lipschitz = new Lipschitz(reporter, solver, leonToZ3)
          getTaylorErrorLipschitz(path.bodyReal, ids, approx.map(a => a.maxError), initErrors, vars,
            And(getClauses(preReal).filter(cl => !belongsToActual(cl) && !isRangeClause(cl))), precision)
        } catch {
          case e: Exception => reporter.warning("Taylor computation failed for " + vc.fncId) ;
        }

      }
      (constraint, specs)
    }

 /*
    Get approximation for results and all intermediate variables.
    Used for proving preconditions.
  */
  private def getApproximationAndSpec_AllVars(path: Path, precision: Precision): Expr = path.bodyFinite match {
    case True => True // noop
    case body =>
      solver.clearCounts
      //start = System.currentTimeMillis
      val approximatorNew = new AAApproximator(reporter, solver, precision, checkPathError, options.lipschitz)
      val approxs: Map[Expr, XReal] = approximatorNew.approximateEquations(body,
        And(vc.pre, path.condition), vc.variables, exactInputs = false)
      //println("new:     " + approxNew)
      //println((System.currentTimeMillis - start) + "ms")

      reporter.info("solver counts: " + solver.getCounts)
      
      val constraint = And(approxs.foldLeft(Seq[Expr]())(
          (seq, kv) => seq ++ Seq(LessEquals(RealLiteral(kv._2.interval.xlo), kv._1),
                                  LessEquals(kv._1, RealLiteral(kv._2.interval.xhi)),
                                  Noise(vc.variables.getIdeal(kv._1), RealLiteral(kv._2.maxError)))))

      constraint
  }

  private def getApproximationAndSpec_LoopInv(path: Path, precision: Precision, preReal: Expr):
    (Expr, Seq[LoopSpec]) = path.bodyFinite match {
    case True => (True, Seq()) // noop
    case body =>
      solver.clearCounts
      
      val (ids: Seq[Identifier], updateFncs) = vc.updateFunctions.unzip

      // this is trying to show that this thing is inductive
      val approximatorNew = new AAApproximator(reporter, solver, precision, checkPathError, options.lipschitz)
      val approxs = approximatorNew.approximateEquations(body,
        And(vc.pre, path.condition), vc.variables, exactInputs = false)
      
      //println("new:     " + approxs)
      
      reporter.info("solver counts for loop invariant: " + solver.getCounts)
      
      val constraint = And(approxs.foldLeft(Seq[Expr]())(
          (seq, kv) => seq ++ Seq(LessEquals(RealLiteral(kv._2.interval.xlo), kv._1),
                                  LessEquals(kv._1, RealLiteral(kv._2.interval.xhi)),
                                  Noise(vc.variables.getIdeal(kv._1), RealLiteral(kv._2.maxError)))))

      //println("constraint: " + constraint)

      // ~~~~~~~~~~~~~ Loop errors ~~~~~~~~~~~~~~~~~~~~~~
      /*val start = System.currentTimeMillis

      val actualRanges: Map[Expr, RationalInterval] = vc.variables.inputs.map({
        case (v @ Variable(_), rec @ Record(idealId, _, _, _, _, _)) =>

          if (vc.variables.integers.contains(idealId)) {
            (Variable(idealId), RationalInterval(rec.lo, rec.up))
          } else if (rec.loAct.isEmpty || rec.upAct.isEmpty) {
            throw new Exception("Loop error computation needs actual ranges!")
          } else {
            (Variable(idealId), RationalInterval(rec.loAct.get, rec.upAct.get))
          }
        
        })

      // Roundoff errors have to be computed over the entire actual range,
      // and inputs are exact
      //println("path condition: " + path.condition)
      val actualRangesPrecondition = rangeConstraintFromIntervals(actualRanges)
      val additionalRealConstraints = And(getAdditionalRealConstraints(vc.pre))
      //println("additionalRealConstraints: " + additionalRealConstraints)
      val (_, sigmas:Seq[Rational])  = approximatorNew.approximateUpdateFncs(body,
        And(actualRangesPrecondition, And(path.condition, additionalRealConstraints)), vc.variables,
        exactInputs = true,
        actualRanges = true,
        updateFncs.map(fnc => idealToActual(fnc, vc.variables)))

      reporter.info("sigmas: " + sigmas)
      
      //println("actualRanges: " + actualRanges)

      val lipschitzCnst = getLipschitzMatrix(path.bodyReal, ids, updateFncs, actualRanges, preReal, precision)
      

      val initialErrors = vc.variables.inputs.map({
        case (_, rec) =>
          if (rec.initialError.isEmpty) (rec.idealId, approxs(rec.actualExpr).maxError)
          else (rec.idealId, rec.initialError.get)
      })
      //println("initial errors: " + initialErrors)
      
      val loopError = vc.loopBound match {
        case Some(n) => computeErrorFromLoopBound(ids, sigmas, n, initialErrors, lipschitzCnst)
        case None =>  Seq()
      }
      reporter.info("loop error computation time: " + (System.currentTimeMillis - start) + "ms")
                

      if(vc.loopBound.nonEmpty && options.loopUnrolling) { //if (options.loopUnrolling) {
        val start2 = System.currentTimeMillis
        val valMap = getValMapForInlining(path.bodyReal)
        val inlinedUp = vc.updateFunctions.map({
          case (id, e) => UpdateFunction(Variable(id), replace(valMap, e))
          })
        //println("inlined update functions: " + inlinedUp)
        val initialVarMap: Map[Expr, Expr] = ids.map(i => (Variable(i), Variable(i))).toMap
        val unrolledLoop = unroll(inlinedUp, vc.loopBound.get, initialVarMap, Seq(), 1)
        //println("unrolledLoop: " + unrolledLoop.mkString("\n"))
        val unrolledResult = approximatorNew.approximate(idealToActual(And(unrolledLoop), vc.variables),
          And(vc.pre, path.condition), vc.variables, exactInputs = false)
        println("unrolledResult: ")
        unrolledResult.foreach{ x =>
          println("\n" + x.interval + ", " + x.maxError)
        }
        reporter.info("loop unrolling time: " + (System.currentTimeMillis - start2) + "ms")
      }

      val loopSpecs = ids.zip(sigmas).zipWithIndex.map({               
        case ((id, sigma), index) =>  // row in lipCnsts corresponds to one update fnc 
          LoopSpec(id, lipschitzCnst.rows(index), sigma, actualRanges(Variable(id)), Some(loopError(index)))
        })
      */
      val loopSpecs = Seq()

      (constraint, loopSpecs)
  }

  private def unroll(updates: Seq[UpdateFunction], max: Int, varMap: Map[Expr, Expr],
    unrolled: Seq[Expr], count: Int): Seq[Expr] = {
    
    if (count >= max) {
      val newUpdates = updates.map({
        case UpdateFunction(lhs, rhs) =>
          replace(varMap, rhs)
        })


      if (updates.length > 1) { unrolled :+ Tuple(newUpdates) }
      else { unrolled :+ newUpdates.head }
    } else {
      //println("loop " + count)
      //println("varMap: " + varMap)
      var newVarMap: Map[Expr, Expr] = Map.empty
      val newUpdates = updates.map({
        case UpdateFunction(lhs, rhs) =>
          val newVal = Variable(FreshIdentifier(lhs.toString + count)).setType(RealType)
          newVarMap += ((lhs -> newVal))
          Equals(newVal, replace(varMap, rhs))
        })
      //println("newUpdates: " + newUpdates)
      //println("newVarMap: " + newVarMap)
      //val newLoop = body  

      unroll(updates, max, newVarMap, unrolled ++ newUpdates, count + 1)
    }


  }

  private def getLipschitzPathError(paths: Seq[Path], precision: Precision): Rational = {
    val carthesianProduct: Seq[(Path, Path)] = paths.flatMap( p1 =>
      paths.filter(p2 => p2 != p1).map(p2 => (p1, p2))
    )

    val lipschitz = new LipschitzPathError(reporter, solver, precision, vc.variables)
    carthesianProduct.foldLeft(zero) {
      case (maxSoFar, (p1, p2)) =>
        lipschitz.computePathError(removeErrors(vc.pre), p1, p2) match {
          case Some(pError) => max( maxSoFar, pError )
          case None => maxSoFar
        }
    }    
  }

  private def removeLoopCounterUpdate(e: Expr): Expr = {
    preMap {
      case Equals(tmp, Plus(c, IntLiteral(1))) => Some(Equals(tmp, PlusR(c, RealLiteral(Rational(1)))))
      case Equals(tmp, PlusR(lc, IntLiteral(1))) if (lc.getType == LoopCounterType) => Some(True)
      case _ => None
    }(e)
  }


  private def validLoopCondition(e: Expr) = e match {
    case LessThan(l, IntLiteral(_)) if(l.getType == LoopCounterType) => true
    case LessThan(v @ Variable(_), IntLiteral(_)) if (vc.variables.isLoopCounter(v)) => true

    case _ =>
      reporter.warning("unrecognized loop condition: " + e)
      false
  }

  

  // Needed for the iteration construct we had
  /*private def inlineBodyForUpdateFncs(body: Expr, updateFncs: Seq[UpdateFunction]): Seq[UpdateFunction] = {
    var valMap: Map[Expr, Expr] = getValMapForInlining(body)
    updateFncs.map( uf => UpdateFunction(uf.lhs, replace(valMap, uf.rhs)))
  }*/

 
  /*
    Replace the function call with its specification. For translation to Z3 FncValue needs to be translated
    with a fresh variable. For approximation, translate the spec into an XFloat.
  */
  private def inlinePostcondition(expr: Expr, precision: Precision, postcondMap: Map[FunDef, Seq[Spec]]): Expr = {
    def extractSpecs(e: Expr, id: Identifier): Option[Spec] = {
      var lwrBoundReal: Option[Rational] = None
      var upBoundReal: Option[Rational] = None
      var lwrBoundActual: Option[Rational] = None
      var upBoundActual: Option[Rational] = None
      var error: Option[Rational] = None
      var extras = List[Expr]()

      
      preTraversal{
        case LessEquals(RealLiteral(lwrBnd), Variable(i)) if (i == id) =>
          lwrBoundReal = Some(lwrBnd)
        case LessEquals(Variable(i), RealLiteral(uprBnd)) if (i == id) => upBoundReal = Some(uprBnd)
        case LessThan(RealLiteral(lwrBnd), Variable(i)) if (i == id) => lwrBoundReal = Some(lwrBnd)
        case LessThan(Variable(i), RealLiteral(uprBnd)) if (i == id) =>  upBoundReal = Some(uprBnd)
        case GreaterEquals(RealLiteral(uprBnd), Variable(i)) if (i == id) =>  upBoundReal = Some(uprBnd)
        case GreaterEquals(Variable(i), RealLiteral(lwrBnd)) if (i == id) => lwrBoundReal = Some(lwrBnd)
        case GreaterThan(RealLiteral(uprBnd), Variable(i)) if (i == id) =>  upBoundReal = Some(uprBnd)
        case GreaterThan(Variable(i), RealLiteral(lwrBnd)) if (i == id) => lwrBoundReal = Some(lwrBnd)

        case LessEquals(RealLiteral(lwrBnd), Actual(Variable(i))) if (i == id) => lwrBoundActual = Some(lwrBnd)
        case LessEquals(Actual(Variable(i)), RealLiteral(uprBnd)) if (i == id) => upBoundActual = Some(uprBnd)
        case LessThan(RealLiteral(lwrBnd), Actual(Variable(i))) if (i == id) => lwrBoundActual = Some(lwrBnd)
        case LessThan(Actual(Variable(i)), RealLiteral(uprBnd)) if (i == id) => upBoundActual = Some(uprBnd)
        case GreaterEquals(RealLiteral(uprBnd), Actual(Variable(i))) if (i == id) => upBoundActual = Some(uprBnd)
        case GreaterEquals(Actual(Variable(i)), RealLiteral(lwrBnd)) if (i == id) => lwrBoundActual = Some(lwrBnd)
        case GreaterThan(RealLiteral(uprBnd), Actual(Variable(i))) if (i == id) => upBoundActual = Some(uprBnd)
        case GreaterThan(Actual(Variable(i)), RealLiteral(lwrBnd)) if (i == id) => lwrBoundActual = Some(lwrBnd)

        case Noise(Variable(i), RealLiteral(value)) if (i == id) => error = Some(value)

        case Times(_, _) | Plus(_, _) | Division(_, _) | Minus(_, _) | UMinus(_) =>
          throw new Exception("found integer arithmetic in ResultCollector")

        case _ => ;
      } (e)

      error match {
        case Some(err) =>
          if ((lwrBoundReal.nonEmpty || lwrBoundActual.nonEmpty) && (upBoundReal.nonEmpty || upBoundActual.nonEmpty)) {
            Some(SimpleSpec(id, RationalInterval(lwrBoundReal.getOrElse(lwrBoundActual.get - err),
               upBoundReal.getOrElse(upBoundActual.get + err)), error))
          } else {
            None
          }
          // if we don't have the error, we cannot convert the actual range into a real one
        case None => 
          if (lwrBoundReal.nonEmpty && upBoundReal.nonEmpty) {
            // we do assume, however, that there is a roundoff error attached
            val rndoff = roundoff(max(lwrBoundReal.get, upBoundReal.get), precision)
            Some(SimpleSpec(id, RationalInterval(lwrBoundReal.get, upBoundReal.get), Some(rndoff)))
          } else {
            reporter.warning("Insufficient information in postcondition for inlining: " + e)
            None
          }
      }
    }

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

    
    preMap {
      case FunctionInvocation(typedFunDef, args) =>
        val funDef = typedFunDef.fd
        val arguments: Map[Expr, Expr] = funDef.params.map(decl => decl.toVariable).zip(args).toMap
        funDef.postcondition.flatMap({
          case (resId, postExpr) =>
            val resFresh = resId.getType match {
              case TupleType(bases) =>
                bases.foldLeft[Seq[Identifier]](Seq())({
                  case (seq, next) => seq :+ getFreshTmpId
                  })
                
              case _ => Seq(getFreshTmpId)
            }
            //println(s"$resFresh")
            // TODO: why are we doing this again? It shoud already be in the fncMap for inlining
            val postcondition = extractPostCondition(resId, postExpr, resFresh)
            //println(s"extracted: $postcondition")

            try {
              val specs: Seq[Spec] = resFresh.map( r => { extractSpecs(postcondition, r).get })
              //println("specs: " + specs)

              val deltaMap: Map[Identifier, Rational] =
                specs.filter(s => s.absError.nonEmpty).map( s => (s.id, s.absError.get)).toMap
              // println("deltaMap: " + deltaMap)
              val realSpecExpr = actualToRealSpec(postcondition, deltaMap)
              //println("realSpecExpr: " + realSpecExpr)

              //println("inlining : " + funDef.id + "   " + funDef.annotations.contains("model"))
              Some(FncValue(specs, realSpecExpr, funDef.annotations.contains("model"), funDef, args))
            } catch {
              case e: Exception =>
                //println("exception " + e)
                //Some(FncValue(Seq.empty, replace(arguments, postcondition)))
                None
            }
        }) match {
          case Some(fncValue) => Some(fncValue)
          case _ => postcondMap.getOrElse(funDef, Seq()) match {
            case specs: Seq[Spec] if specs.nonEmpty =>
              val specsExpr = And(specs.map(_.toExpr))
              Some(FncValue(specs, replace(arguments, specsExpr), funDef.annotations.contains("model"), funDef, args))
            case _ =>
              throw PostconditionInliningFailedException("missing postcondition for " + funDef.id.name);
              null
          }
        }

      case _ => None
    }(expr)
  }
    
}

object Approximations {




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
