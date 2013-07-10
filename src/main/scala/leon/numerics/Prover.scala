package leon
package numerics

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._

import affine._
import affine.XFloat._

import Utils._
import VariableShop._

import Sat._
import Valid._
import ApproximationType._
import Precision._


class Prover(reporter: Reporter, ctx: LeonContext, program: Program, precision: Precision, specgen: Boolean, timeout: Long) {
  val verbose = false
  val deltaRemover = new DeltaRemover
  val noiseRemover = new NoiseRemover
  val solver = new NumericSolver(ctx, program, timeout)
  var postInliner = new PostconditionInliner(reporter, Map.empty) // dummy
  var fullInliner = new FullInliner(reporter, Map.empty) //dummy
  val resultCollector = new ResultCollector
  var xevaluator = new XEvaluator(reporter, solver, precision, Map.empty) //dummy

  val printStats = true

  val unitRoundoff = getUnitRoundoff(precision)
  val unitRoundoffDefault = getUnitRoundoff(Float64)

  def check(inputVC: VerificationCondition, vcMap: Map[FunDef, VerificationCondition]): VerificationCondition = {
    reporter.info("")
    reporter.info("----------> checking VC of " + inputVC.funDef.id.name)
    val vc: VerificationCondition = inputVC.copy(allConstraints = inputVC.allConstraints.map(c => c.copy()))

    postInliner = new PostconditionInliner(reporter, vcMap)
    fullInliner = new FullInliner(reporter, vcMap)
    xevaluator = new XEvaluator(reporter, solver, precision, vcMap)

    val start = System.currentTimeMillis
    for (c <- vc.allConstraints) {
      reporter.info("----------> checking constraint: " + c.description)
      if (verbose) {println("pre: " + c.pre); println("body: " + c.body); println("post: " + c.post)}

      while (c.hasNextApproximation && !c.solved) {
        val next = c.getNextApproxType.get
        reporter.info("Computing approximation: " + next)
        getNextApproximation(next, c, vc.inputs) match {
          case Some(approx) =>
            //println("Approx: " + approx)
            c.approximations = Seq(approx) ++ c.approximations
            if (approx.paths.size > 1)
              c.overrideStatus(checkWithZ3PathWise(approx, vc.allVariables))
            else
              c.overrideStatus(checkWithZ3OneConstraint(approx, vc.allVariables))
            //c.overrideStatus(checkWithZ3(approx, vc.allVariables))
            reporter.info("RESULT: " + c.status)
          case None =>
            reporter.info("Skipping approximation, None returned.")
        }
      }
    }

    reporter.info("Now computing the postcondition.")
    //try {
      vc.specConstraint match {
        case Some(sC) =>
          vc.generatedPost = Some(getPost(sC, vc.inputs))
          reporter.info("Generated post: " + vc.generatedPost)
        case None =>
          reporter.info("Skipping spec gen on this one")
      }
    //} catch {case _=> ;}

    val totalTime = (System.currentTimeMillis - start)
    vc.verificationTime = Some(totalTime)
    vc
  }

  /* *************************
        Verification
  **************************** */
  private def checkWithZ3OneConstraint(ca: ConstraintApproximation, parameters: Seq[Variable]): Option[Valid] = {
    //println("Choosing one constraint version")
    val (resVar, eps, buddies) = getVariables(parameters ++ ca.vars)
    val trans = new NumericConstraintTransformer(buddies, resVar, eps, RoundoffType.RoundoffMultiplier, reporter)
    val precondition =  if (ca.addInitialVariableConnection) trans.transformCondition(ca.pre)
                       else trans.transformCondition(noiseRemover.transform(ca.pre))
    val postcondition = trans.transformCondition(ca.post)

    var (idealPart, actualPart) = (Seq[Expr](), Seq[Expr]())
    for(path <- ca.paths) {
      val aI = trans.transformIdealBlock(path.idealBody)
      idealPart = idealPart :+ And(And(path.pathCondition, trans.transformCondition(path.idealCnst)), aI)
      val nN = trans.transformNoisyBlock(path.actualBody)
      actualPart = actualPart :+ And(And(trans.getNoisyCondition(path.pathCondition), trans.transformCondition(path.actualCnst)), nN)
    }
    val machineEpsilon = Equals(eps, RationalLiteral(unitRoundoff))

    val body =
      if(ca.needEps) And(And(Or(idealPart), Or(actualPart)), machineEpsilon)
      else And(Or(idealPart), Or(actualPart))

    var toCheck = ArithmeticOps.totalMakeover(And(And(precondition, body), negate(postcondition) ))
    //var toCheck = And(And(precondition, body), negate(postcondition))
    println("\nTO CHECK:\n" + deltaRemover.transform(toCheck))

    if (reporter.errorCount == 0 && sanityCheck(precondition, false, body))
      solver.checkSat(toCheck) match {
        case (UNSAT, _) => Some(VALID)
        case (SAT, model) =>
          println("Model found: " + model)
          // TODO: print the models that are actually useful, once we figure out which ones those are
          Some(UNKNOWN)
        case _ =>
          Some(UNKNOWN)
      }
    else
      None
  }

  private def checkWithZ3PathWise(ca: ConstraintApproximation, parameters: Seq[Variable]): Option[Valid] = {
    val (resVar, eps, buddies) = getVariables(parameters ++ ca.vars)
    val trans = new NumericConstraintTransformer(buddies, resVar, eps, RoundoffType.RoundoffMultiplier, reporter)
    val precondition =  if (ca.addInitialVariableConnection) trans.transformCondition(ca.pre)
                       else trans.transformCondition(noiseRemover.transform(ca.pre))
    val postcondition = trans.transformCondition(ca.post)
    val machineEpsilon = Equals(eps, RationalLiteral(unitRoundoff))
    var allProven = true

    for (path <- ca.paths) {
      val aI = trans.transformIdealBlock(path.idealBody)
      val idealPart = And(And(path.pathCondition, trans.transformCondition(path.idealCnst)), aI)
      val nN = trans.transformNoisyBlock(path.actualBody)
      val actualPart = And(And(trans.getNoisyCondition(path.pathCondition), trans.transformCondition(path.actualCnst)), nN)
      val body =
        if(ca.needEps) And(And(idealPart, actualPart), machineEpsilon)
          else And(idealPart, actualPart)

      var toCheck = ArithmeticOps.totalMakeover(And(And(precondition, body), negate(postcondition)))

      //var toCheck = And(And(precondition, body), negate(postcondition))
      //println("\nTO CHECK:\n" + deltaRemover.transform(toCheck))
      if (reporter.errorCount == 0 && sanityCheck(precondition, false, body))
        solver.checkSat(toCheck) match {
          case (UNSAT, _) => path.status = Some(VALID)
          case (SAT, model) =>
            allProven = false
            //println("Model found: " + model)
            // TODO save this somewhere so we can emit the appropriate runtime checks
            path.status = Some(UNKNOWN)
          case _ =>
            path.status = Some(UNKNOWN)
            allProven = false
        }
      else allProven = false
    }
    if (allProven) Some(VALID)
    else Some(UNKNOWN)
  }




  /*val eps2 = Variable(FreshIdentifier("#eps2")).setType(RealType)
    val boundsConverter = new BoundsConverter(eps2, eps)
    val toCheck2 = boundsConverter.transform(toCheck)
    println("\n new to Check:")
    println(toCheck2)
    //toCheck = toCheck2*/


  // if true, we're sane
  private def sanityCheck(pre: Expr, silent: Boolean = true, body: Expr = BooleanLiteral(true)): Boolean = {
    val sanityCondition = And(pre, body)
    solver.checkSat(sanityCondition) match {
      case (SAT, model) =>
        //if (!silent) reporter.info("Sanity check passed! :-)")
        //reporter.info("model: " + model)
        true
      case (UNSAT, model) =>
        if (!silent) reporter.warning("Not sane! " + sanityCondition)
        false
      case _ =>
        reporter.info("Sanity check failed! ")// + sanityCondition)
        false
    }
  }


  /* *************************
        Approximations
  **************************** */

  // TODO: we can cache some of the body transforms and reuse for AA...
  def getNextApproximation(tpe: ApproximationType, c: Constraint, inputs: Map[Variable, Record]): Option[ConstraintApproximation] = tpe match {
    /* ******************
       NO APPROXIMATION
    * ******************* */
    case Uninterpreted_None =>
      val paths = collectPaths(c.body).map(p => APath(p.condition, And(p.expression), True, And(p.expression), True, p.values))
      Some(ConstraintApproximation(c.pre, paths, c.post, Set.empty, tpe))

    case PostInlining_None =>
      postInliner.inlinePostcondition(c.pre, c.body, c.post) match {
        case Some((newPre, newBody, newPost, vars)) =>
          Some(ConstraintApproximation(newPre,
            collectPaths(newBody).map(p => APath(p.condition, And(p.expression), True, And(p.expression), True, p.values)),
            newPost, vars, tpe))
        case None => None
      }

    case FullInlining_None =>
      val (newPre, newBody, newPost, vars) = fullInliner.inlineFunctions(c.pre, c.body, c.post)
      val paths = collectPaths(newBody).map(p => APath(p.condition, And(p.expression), True, And(p.expression), True, p.values))
      Some(ConstraintApproximation(newPre, paths, newPost, vars, tpe))

    /* ******************
       With APPROXIMATION
    * ******************* */
    case NoFncs_AA_Merging =>
      try {
        val body = c.body
        val filteredPrecondition = filterPreconditionForBoundsIteration(c.pre)
        //println("body: " + body)
        val (xfloats, indices) = xevaluator.evaluate(body, filteredPrecondition, inputs)
        //println("xfloats: " + xfloats)
        val apaths = Set(APath(True, True, body, True, constraintFromXFloats(xfloats), xfloats))
        println("computed constraint: " + constraintFromXFloats(xfloats))
        val cApprox = ConstraintApproximation(c.pre, apaths, c.post, Set.empty, tpe)
        cApprox.needEps = false
        cApprox.addInitialVariableConnection = false
        return Some(cApprox)
      }  catch {
        case x =>
          reporter.warning("Exception: " + x)
          reporter.warning(x.getStackTrace)
      }
      None

    // Fallback
    case NoFncs_AAOnly_Merging =>
      findApproximation(c, inputs, NoFncs_AA_Merging) match {
        case Some(ConstraintApproximation(pre, apaths, post, vars, typpe, values)) =>
          val resConstraint = constraintFromXFloats(Map(ResultVariable() -> apaths.head.xfloats(ResultVariable())))
          val apathsNew = Set(APath(True, True, True, True, resConstraint, apaths.head.xfloats))
          val cApprox = ConstraintApproximation(pre, apathsNew, post, vars, tpe)
          cApprox.needEps = false
          cApprox.addInitialVariableConnection = false
          Some(cApprox)
        case None => None
      }

    case NoFncs_AA =>
      try {
        val paths = c.paths
        val filteredPrecondition = filterPreconditionForBoundsIteration(c.pre)
        
        val apaths = paths.collect {
          case path: Path if (sanityCheck(And(path.condition, filteredPrecondition), false)) =>
            val fullPathCondition = And(path.condition, filteredPrecondition)

            //println("fullPathCondition: " + fullPathCondition)
            val eps2 = Variable(FreshIdentifier("#eps2")).setType(RealType)
            val boundsConverter = new BoundsConverter(eps2, eps2)
            val newPathCond = boundsConverter.transform(fullPathCondition)
            //println("\n new cond: " + newPre)

            val (resConstraint, xfloatMap) =
              if(And(path.expression) == True) { (True, Map[Expr, XFloat]()) }
              else {
                val (xfloats, indices) = xevaluator.evaluate(And(path.expression), newPathCond, inputs)
                println(noiseConstraintFromXFloats(xfloats))
                (noiseConstraintFromXFloats(xfloats), xfloats)
                // TODO: can we find out when we don't need the full constraint, only for res?
                // Like when it's an invariant we need full, else only res?
                //Noise(ResultVariable(), RationalLiteral(xfloats(ResultVariable()).maxError))
              }
            APath(path.condition,
              True, And(path.expression),
              True, resConstraint, xfloatMap)
        }
        // TODO: do we want to also collect those paths we skip? for info reasons?
        if (apaths.size > 0) { // at least one feasible path
          val cApprox = ConstraintApproximation(c.pre, apaths, c.post, Set.empty, tpe)
          cApprox.needEps = false
          cApprox.addInitialVariableConnection = false
          return Some(cApprox)
        } else {
          None
        }
      } catch {
        case x =>
          reporter.warning("Exception: " + x)
          reporter.warning(x.getStackTrace)
      }
      None

    // Fallback
    case NoFncs_AAOnly =>
      findApproximation(c, inputs, NoFncs_AA) match {
        case Some(ConstraintApproximation(pre, apaths, post, vars, typpe, values)) =>
          val apathsNew = apaths.map {
            case APath(pathCondition, idealBody, idealCnst, actualBody, actualCnst, xfloats) =>
              val resConstraint = constraintFromXFloats(Map(ResultVariable() -> xfloats(ResultVariable())))
              APath(pathCondition, True, True, True, resConstraint, xfloats)
          }
          val cApprox = ConstraintApproximation(pre, apathsNew, post, vars, tpe)
          cApprox.needEps = false
          cApprox.addInitialVariableConnection = false
          return Some(cApprox)
        case None => None
      }


    case FullInlining_AA_Merging =>
      try {
        val (newPre, newBody, newPost, vars) = fullInliner.inlineFunctions(c.pre, c.body, c.post)
        val filteredPrecondition = filterPreconditionForBoundsIteration(newPre)
        val (xfloats, indices) = xevaluator.evaluate(newBody, filteredPrecondition, inputs)

        val apaths = Set(APath(True, newBody, True, True, noiseConstraintFromXFloats(xfloats), xfloats))
        val cApprox = ConstraintApproximation(newPre, apaths, newPost, vars, tpe)
        cApprox.needEps = false
        cApprox.addInitialVariableConnection = false
        return Some(cApprox)
      } catch {
        case x =>
          reporter.warning("Exception: " + x)
          reporter.warning(x.getStackTrace)
      }
      None

    case FullInlining_AAOnly_Merging =>
      findApproximation(c, inputs, FullInlining_AA_Merging) match {
        case Some(ConstraintApproximation(pre, apaths, post, vars, typpe, values)) =>
          val resConstraint = constraintFromXFloats(Map(ResultVariable() -> apaths.head.xfloats(ResultVariable())))
          val apathsNew = Set(APath(True, True, True, True, resConstraint, apaths.head.xfloats))
          val cApprox = ConstraintApproximation(pre, apathsNew, post, vars, tpe)
          cApprox.needEps = false
          cApprox.addInitialVariableConnection = false
          return Some(cApprox)
        case None => None
      }


    case FullInlining_AA =>
      try {
        val (newPre, newBody, newPost, vars) = fullInliner.inlineFunctions(c.pre, c.body, c.post)

        val paths = collectPaths(newBody)
        val newInputs = getVariableRecords(newPre)
        val filteredPrecondition = filterPreconditionForBoundsIteration(newPre)
        //println("paths: " + paths.mkString("\n"))
        val apaths = paths.collect {
          case path: Path if (sanityCheck(And(path.condition, filteredPrecondition))) =>
            //println("Computing for path: " )//+ path)
            val fullPathCondition = And(path.condition, filteredPrecondition)
            //println("fullPathCondition: " + fullPathCondition)

            val (resConstraint, xfloatMap) =
              if(And(path.expression) == True) { (True, Map[Expr, XFloat]()) }
              else {
                val (xfloats, indices) = xevaluator.evaluate(And(path.expression), fullPathCondition, newInputs)
                println("resConstraint: " + constraintFromXFloats(xfloats))
                
                (noiseConstraintFromXFloats(xfloats), xfloats)
                //TODO: see above
                //Noise(ResultVariable(), RationalLiteral(xfloats(ResultVariable()).maxError))
              }
            APath(path.condition,
              True, And(path.expression),
              True, resConstraint, xfloatMap)
        }
        if (apaths.size > 0) { // at least one feasible path
          val cApprox = ConstraintApproximation(newPre, apaths, newPost, vars, tpe) //not sure what the vars here will be good for
          cApprox.needEps = false
          cApprox.addInitialVariableConnection = false
          return Some(cApprox)
        } else {
          None
        }
      } catch {
        case x =>
          reporter.warning("Exception: " + x)
          reporter.warning(x.getStackTrace)
      }
      None

    case FullInlining_AAOnly =>
      findApproximation(c, inputs, FullInlining_AA) match {
        case Some(ConstraintApproximation(pre, apaths, post, vars, typpe, values)) =>
          val apathsNew = apaths.map {
            case APath(pathCondition, idealBody, idealCnst, actualBody, actualCnst, xfloats) =>
              val resConstraint = constraintFromXFloats(Map(ResultVariable() -> xfloats(ResultVariable())))
              APath(pathCondition, True, True, True, resConstraint, xfloats)
          }
          val cApprox = ConstraintApproximation(pre, apathsNew, post, vars, tpe)
          cApprox.needEps = false
          cApprox.addInitialVariableConnection = false
          return Some(cApprox)
        case None => None
      }

    /*
    TODO: still doesn't work. The errors on the intial variables have to be written with err_sth
    case PostInlining_AA =>
      //try {
        val paths = c.paths
        val filteredPrecondition = filterPreconditionForBoundsIteration(c.pre)
        var newVariables = Set[Variable]()
        val apaths = paths.collect {
          case path: Path if (sanityCheck(And(path.condition, filteredPrecondition), false)) =>
            val fullPathCondition = And(path.condition, filteredPrecondition)

            val (resConstraint, xfloatMap) =
              if(And(path.expression) == True) { (True, Map[Expr, XFloat]()) }
              else {
                val (xfloats, indices) = xevaluator.evaluate(And(path.expression), fullPathCondition, inputs)
                (noiseConstraintFromXFloats(xfloats), xfloats)
                // TODO: can we find out when we don't need the full constraint, only for res?
                // Like when it's an invariant we need full, else only res?
                //Noise(ResultVariable(), RationalLiteral(xfloats(ResultVariable()).maxError))
              }
            val (newBody, bodyCnstrs, vars) = postInliner.inlineFncPost(And(path.expression))
            newVariables ++= vars
            APath(path.condition,
              True, And(bodyCnstrs :+ newBody),
              True, resConstraint, xfloatMap)
        }
        // TODO: do we want to also collect those paths we skip? for info reasons?
        if (apaths.size > 0) { // at least one feasible path
          val (newPost, postCnstrs, vars) = postInliner.inlineFncPost(c.post)

          val cApprox = ConstraintApproximation(And(c.pre, And(postCnstrs)), apaths, newPost, newVariables ++ vars, tpe)
          cApprox.needEps = false
          cApprox.addInitialVariableConnection = false
          return Some(cApprox)
        } else {
          None
        }
      /*} catch {
        case x =>
          reporter.warning("PostInlining_AA throws: " + x)
          reporter.warning(x.getStackTrace)
      }
      None*/
    */

      // TODO: if Z3 still fails, do the full approximation, also for the range with AA
      // for this we should only reuse already computed approximations

  }

  /* *************************
    Specification Generation.
  **************************** */
  // TODO: provenPost is without roundoff errors!
  private def getMostPrecise(provenPost: Expr, values: Map[Expr, (RationalInterval, Rational)]): Expr = {
    import Rational.{min, max}
    val (compInt, compErr) = values(ResultVariable())

    val (lwrBnd, upBnd, error) = resultCollector.getResult(provenPost) match {
      case (Some(l), Some(u), Some(err)) =>
        (max(l, compInt.xlo), min(u, compInt.xhi), min(err, compErr))

      case (Some(l), Some(u), None) =>
        (max(l, compInt.xlo), min(u, compInt.xhi), compErr)
      case (Some(l), None, Some(err)) =>
        (max(l, compInt.xlo), compInt.xhi, min(err, compErr))
      case (None, Some(u), Some(err)) =>
        (compInt.xlo, min(u, compInt.xhi), min(err, compErr))

      case (Some(l), None, None) =>
        (max(l, compInt.xlo), compInt.xhi, compErr)
      case (None, Some(u), None) =>
        (compInt.xlo, min(u, compInt.xhi), compErr)
      case (None, None, Some(err)) =>
        (compInt.xlo, compInt.xhi, min(err, compErr))
      case _=> (compInt.xlo, compInt.xhi, compErr)
    }
    constraintFromResults(Map(ResultVariable() -> (RationalInterval(lwrBnd, upBnd), error)))
  }


  private def getPost(c: Constraint, inputs: Map[Variable, Record]): Expr = {
    val approxType = (c.hasFunctionCalls, c.merging) match {
      case (false, true) => NoFncs_AA_Merging
      case (false, false) => NoFncs_AA
      case (true, true) => FullInlining_AA_Merging
      case (true, false) => FullInlining_AA
    }

    (findApproximation(c, inputs, approxType), c.status) match {
      case (Some(approx), Some(VALID)) =>
        constraintFromResults(Map(ResultVariable() -> approx.actualXfloats(ResultVariable())))
        // TODO: getMostPrecise(c.post, approx.values)
      case (Some(approx), _) => constraintFromResults(Map(ResultVariable() -> approx.actualXfloats(ResultVariable())))
      case (None, Some(VALID)) => c.post
      case (None, _) => True
    }
  }

  private def findApproximation(c: Constraint, inputs: Map[Variable, Record], tpe: ApproximationType): Option[ConstraintApproximation] = {
    c.approximations.find(a => tpe == a.tpe) match {
      case Some(app) => Some(app)
      case None => getNextApproximation(tpe, c, inputs)
    }
  }



  /* *************************
            Utils
  **************************** */
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
    case Noise(_, _) => True
    case Roundoff(_) => True
    case RelError(_, _) => True
    case _ => expr
  }




  /*

    case PostInlining_AA =>
      postInliner.inlinePostcondition(c.pre, c.body, c.post) match {
        case Some((newPre, newBody, newPost, vars)) =>
          val (newConstraint, apaths, values) = computeApproxForRes(collectPaths(newBody), newPre, getVariableRecords(newPre))
          Some(ConstraintApproximation(And(newPre, newConstraint), apaths, newPost, vars, tpe, values))

        case None => None
      }


    case PostInlining_AAPathSensitive =>
      postInliner.inlinePostcondition(c.pre, c.body, c.post) match {
        case Some((newPre, newBody, newPost, vars)) =>
          val paths = collectPaths(newBody)
          for (p <- paths) computeApproximation(p, newPre, getVariableRecords(newPre))
          val apaths = paths.collect {
            case p: Path if (p.feasible) => getAPath(p).updateNoisy(True, constraintFromXFloats(p.values))
          }
          Some(ConstraintApproximation(newPre, apaths, newPost, vars, tpe))

        case None => None
      }
  }*/
  /*private def checkWithVariablePrecision(ca: ConstraintApproximation, parameters: Seq[Variable]): (Option[Valid], Option[Map[Identifier, Expr]]) = {
    val (resVar, eps, buddies) = getVariables(parameters ++ ca.vars)
    val trans = new NumericConstraintTransformer(buddies, resVar, eps, RoundoffType.RoundoffMultiplier, reporter)
    val precondition = trans.transformCondition(ca.pre)
    val postcondition = trans.transformCondition(ca.post)

    var (idealPart, actualPart) = (Seq[Expr](), Seq[Expr]())
    for(path <- ca.paths) {
      val (aI, nI) = trans.transformBlock(path.idealBody)
      idealPart = idealPart :+ And(And(path.pathCondition, trans.transformCondition(path.idealCnst)), aI)
      val (aN, nN) = trans.transformBlock(path.actualBody)
      actualPart = actualPart :+ And(And(trans.getNoisyCondition(path.pathCondition), trans.transformCondition(path.actualCnst)), nN)
    }

    val body = And(Or(idealPart), Or(actualPart))

    val resultError = Equals(getNewResErrorVariable, Minus(resVar, buddies(resVar))) // let z3 give us error explicitly
    val machineEpsilonWanted = Equals(eps, RationalLiteral(unitRoundoff))
    val machineEpsilonDefault = Equals(eps, RationalLiteral(unitRoundoffDefault))

    val toCheck = And(And(precondition, resultError), Not(postcondition))
    //val toCheck = Implies(And(precondition, And(body, And(resultError, machineEpsilon))), postcondition)
    println("toCheck: " + toCheck)

    val firstTry = if (reporter.errorCount == 0 && sanityCheck(precondition, body)) {
      solver.push
      solver.assertCnstr(toCheck)
      val (res, model) = solver.checkSat(machineEpsilonWanted)

      solver.pop
      println("first try: " + res)
      (Some(res), model)
    } else {
      (None, None)
    }

    // So at this point, all paths should be feasible
    firstTry match {
      case (Some(VALID), _) => firstTry
      case _ => // try again
        val paths = idealPart.zip(actualPart)
        for ((i, a) <- paths) {
          val cnstr = Implies(And(precondition, And(And(i, a), And(resultError, machineEpsilon))), postcondition)
          println("checking path: " + And(i, a))
          val (res, model) = solver.checkValid(cnstr)
          println("with result: " + res)
          if (res != VALID) {
            reporter.info("path could not be proven: " + And(i, a))
            return (Some(res), model)
          }
        }
    }
    (Some(VALID), None)
  }*/

/*def generateSpecMoreInfo(vc: VerificationCondition) = {
    reporter.info("")
    reporter.info("----------> generating postcondition for: " + vc.funDef.id.name)

    // TODO: what do we do with invariants?
    vc.specConstraint match {
      case Some(c) =>
        var args = Seq[Expr]()
        for (path <- c.paths) {
          // TODO: add error on computing the path condition
          val cond = path.condition
          val res = path.values(ResultVariable())

          res.interval

          val errorExpr = getErrorExpression(res.error, path.indices)
          args = args :+ And(Seq(cond, LessEquals(RationalLiteral(res.interval.xlo), ResultVariable()),
            LessEquals(ResultVariable(), RationalLiteral(res.interval.xhi)),
            Noise(ResultVariable(), errorExpr)))
        }


        val newConstraint = Or(args)
        reporter.info("computed spec: " + newConstraint)
        vc.generatedPost = Some(newConstraint)

      case None =>
        reporter.warning("Forgotten spec constraint?")
    }
  }

  def getErrorExpression(a: XRationalForm, indices: Map[Int, Expr]): Expr = {
    val indexSet: Set[Int] = indices.keys.toSet
    val (lin, rest) = a.noise.partition(d => indexSet(d.index))

    val maxError = affine.Utils.sumSeq(rest)
    val restError = RationalInterval(-maxError, maxError) + RationalInterval(a.x0, a.x0)

    val restErrorVar = getNewErrorVar
    var cnstr: Expr = restErrorVar

    for (dev <- lin) {
      // TODO: not quite right! it should be the error on variable, or rather whether it was there or not...
      cnstr = Plus(cnstr, Times(RationalLiteral(dev.value), getNamedError(indices(dev.index))))
    }
    And(ratint2expr(restError, restErrorVar), cnstr)
  }*/


}
