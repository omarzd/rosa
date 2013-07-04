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


class Prover(reporter: Reporter, ctx: LeonContext, program: Program, precision: Precision, specgen: Boolean) {
  val verbose = false
  val deltaRemover = new DeltaRemover
  val noiseRemover = new NoiseRemover
  val solver = new NumericSolver(ctx, program)
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
      if (specgen && !(vc.isInvariant || vc.nothingToCompute)) {
        val mainCnstr = if(vc.allConstraints.size > 0) vc.allConstraints.head
          else Constraint(vc.precondition, vc.body, True, "wholebody")
        vc.generatedPost = Some(getPost(mainCnstr, vc.inputs))

        reporter.info("Generated post: " + vc.generatedPost)
      } else
        reporter.info("Skipping spec gen on this one")
    //} catch {case _=> ;}

    val totalTime = (System.currentTimeMillis - start)
    vc.verificationTime = Some(totalTime)
    vc
  }


  private def checkWithZ3OneConstraint(ca: ConstraintApproximation, parameters: Seq[Variable]): Option[Valid] = {
    println("Choosing one constraint version")
    val (resVar, eps, buddies) = getVariables(parameters ++ ca.vars)
    val trans = new NumericConstraintTransformer(buddies, resVar, eps, RoundoffType.RoundoffMultiplier, reporter)
    // TODO: constraint.addInitialVariableConnection
    //val precondition =  if (ca.addInitialVariableConnection) trans.transformCondition(ca.pre)
    //                   else trans.transformCondition(noiseRemover.transform(ca.pre))
    val precondition = trans.transformCondition(ca.pre)
    val postcondition = trans.transformCondition(ca.post)

    // TODO: errors on computing the path condition?

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

    //TODO: somehow remove redundant definitions of errors? stuff like And(Or(idealPart), Or(actualPart))
    var toCheck = ArithmeticOps.totalMakeover(And(And(precondition, body), Not(postcondition))) //has to be unsat
    println("toCheck: " + deltaRemover.transform(toCheck))

    if (reporter.errorCount == 0 && sanityCheck(precondition, false, body))
      solver.checkSat(toCheck) match {
        case (UNSAT, _) => Some(VALID)
        case (SAT, model) =>
          println("Model found: " + model)
          // TODO: print the models that are actually useful, once we figure out which ones those are
          Some(NOT_SURE)
        case _ =>
          Some(NOT_SURE)
      }
    else
      None
  }

  private def checkWithZ3PathWise(ca: ConstraintApproximation, parameters: Seq[Variable]): Option[Valid] = {
    val (resVar, eps, buddies) = getVariables(parameters ++ ca.vars)
    val trans = new NumericConstraintTransformer(buddies, resVar, eps, RoundoffType.RoundoffMultiplier, reporter)
    // TODO: constraint.addInitialVariableConnection
    //val precondition =  if (ca.addInitialVariableConnection) trans.transformCondition(ca.pre)
    //                   else trans.transformCondition(noiseRemover.transform(ca.pre))
    val precondition = trans.transformCondition(ca.pre)
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
      //TODO: somehow remove redundant definitions of errors? stuff like And(Or(idealPart), Or(actualPart))
      var toCheck = ArithmeticOps.totalMakeover(And(And(precondition, body), Not(postcondition))) //has to be unsat
      println("toCheck: " + deltaRemover.transform(toCheck))
      if (reporter.errorCount == 0 && sanityCheck(precondition, false, body))
        solver.checkSat(toCheck) match {
          case (UNSAT, _) => path.status = Some(VALID)
          case (SAT, model) =>
            allProven = false
            println("Model found: " + model)
            // TODO save this somewhere so we can emit the appropriate runtime checks
            path.status = Some(NOT_SURE)
          case _ =>
            path.status = Some(NOT_SURE)
            allProven = false
        }
      else allProven = false
    }
    if (allProven) Some(VALID)
    else Some(NOT_SURE)
  }


  /* *************************
        Verification
  **************************** */
  // TODO: SPLIT into one that does the full one and another one that goes path-by-path
  private def checkWithZ3(ca: ConstraintApproximation, parameters: Seq[Variable]): (Option[Valid], Option[Map[Identifier, Expr]]) = {
    val (resVar, eps, buddies) = getVariables(parameters ++ ca.vars)
    val trans = new NumericConstraintTransformer(buddies, resVar, eps, RoundoffType.RoundoffMultiplier, reporter)
    // TODO: constraint.addInitialVariableConnection
    //val precondition =  if (ca.addInitialVariableConnection) trans.transformCondition(ca.pre)
    //                   else trans.transformCondition(noiseRemover.transform(ca.pre))
    val precondition = trans.transformCondition(ca.pre)
    val postcondition = trans.transformCondition(ca.post)

    // TODO: errors on computing the path condition?

    var (idealPart, actualPart) = (Seq[Expr](), Seq[Expr]())
    for(path <- ca.paths) {
      val aI = trans.transformIdealBlock(path.idealBody)
      idealPart = idealPart :+ And(And(path.pathCondition, trans.transformCondition(path.idealCnst)), aI)
      val nN = trans.transformNoisyBlock(path.actualBody)
      actualPart = actualPart :+ And(And(trans.getNoisyCondition(path.pathCondition), trans.transformCondition(path.actualCnst)), nN)
    }
    val machineEpsilon = Equals(eps, RationalLiteral(unitRoundoff))

    println("idealPart.size = " + idealPart.size)
    val firstTry =
      if(idealPart.size <= 1) {
        val body =
          if(ca.needEps) And(And(Or(idealPart), Or(actualPart)), machineEpsilon)
          else And(Or(idealPart), Or(actualPart))

          //TODO: somehow remove redundant definitions of errors? stuff like And(Or(idealPart), Or(actualPart))
          var toCheck = ArithmeticOps.totalMakeover(And(And(precondition, body), Not(postcondition))) //has to be unsat
          //println("toCheck: " + deltaRemover.transform(toCheck))

          if (reporter.errorCount == 0 && sanityCheck(precondition, false, body))
            solver.checkSat(toCheck)
          else
            (None, None)
      } else {
        println("Skipping all in.")
        (None, None)
      }
    println("first try: " + firstTry._1)

    firstTry match {
      case (UNSAT, _) => (Some(VALID), None)
      case _ => // try again for each part separately
        if (ca.paths.size > 1) {
          val paths = idealPart.zip(actualPart)
          for ((i, a) <- paths) {
            println("\n checking path: " )//+ deltaRemover.transform(And(i, a)))
            val toCheck = ArithmeticOps.totalMakeover(And(Seq(precondition, i, a, machineEpsilon, Not(postcondition))))
            println("toCheck:" + toCheck)
            val (sat, model) = solver.checkSat(toCheck)
            println("with result: " + sat)
            // TODO: print the models that are actually useful, once we figure out which ones those are
            if (sat != UNSAT) {
              // TODO save this somewhere so we can emit the appropriate runtime checks
              reporter.info("path could not be proven")
              return (Some(NOT_SURE), None)
            }
          }
        } else {
          return (Some(NOT_SURE), None)
        }
    }
    (Some(VALID), None)
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
    //println("Checking condition: " + sanityCondition)
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
    // TODO: Z3 only for the very small cases (some heuristic here to select which ones)

    case NoFncs_AA => // we'll make this by default path sensitive
      try {
        val paths = c.paths
        val filteredPrecondition = filterPreconditionForBoundsIteration(c.pre)
        //println("paths: " + paths.mkString("\n"))
        val apaths = paths.collect {
          case path: Path if (sanityCheck(And(path.condition, filteredPrecondition), false)) =>
            //println("Computing for path: " + path)
            val fullPathCondition = And(path.condition, filteredPrecondition)
            //println("fullPathCondition: " + fullPathCondition)

            val (resConstraint, xfloatMap) =
              if(And(path.expression) == True) { (True, Map[Expr, XFloat]()) }
              else {
                val (xfloats, indices) = xevaluator.evaluate(path.expression, fullPathCondition, inputs)
                //println("xfloats: " + xfloats)
                (noiseConstraintFromXFloats(xfloats), xfloats)
                // TODO: can we find out when we don't need the full constraint, only for res?
                // Like when it's an invariant we need full, else only res?
                //Noise(ResultVariable(), RationalLiteral(xfloats(ResultVariable()).maxError))
              }
            println("resConstraint: " + resConstraint)
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
          reporter.warning("NoFncs_AA throws: " + x)
          reporter.warning(x.getStackTrace)
      }
      None

    // So, now we have functions, two options:
    // 1) inline the function body first, and then do approximation with compacting
    // 2) do the compacting on the fly with every function call

    // This is the second option
    case FullInlining_AACompactOnFnc =>
      try {
        // TODO: inline pre and post? how about invariants?
        val paths = c.paths
        val filteredPrecondition = filterPreconditionForBoundsIteration(c.pre)
        val apaths = paths.collect {
          case path: Path if (sanityCheck(And(path.condition, filteredPrecondition))) =>
            val fullPathCondition = And(path.condition, filteredPrecondition)
            val (xfloats, indices) = xevaluator.evaluateWithFncCalls(path.expression, fullPathCondition, inputs)
            val resNoise = noiseConstraintFromXFloats(xfloats)
            // TODO: see above
            //Noise(ResultVariable(), RationalLiteral(path.values(ResultVariable()).maxError))

            //ideal part, needs fncs inlined
            //println("path cond: " + path.condition)
            //println("body: " + path.expression)
            //TODO: what happened to the vars here?
            val (newPre, newBody, newPost, vars) = fullInliner.inlineFunctions(path.condition, And(path.expression), True)

            //println("newPre: " + newPre)
            //println("newBody: " + newBody)
            //println("newPost: " + newPost)
            APath(newPre,
             True, newBody,
             True, resNoise, xfloats)
        }
        if (apaths.size > 0) { // at least one feasible path
          val cApprox = ConstraintApproximation(c.pre, apaths, c.post, Set.empty, tpe)
          cApprox.needEps = false
          cApprox.addInitialVariableConnection = false
          return Some(cApprox)
        } else {
          None
        }
      } catch { case _=> ;}
      None

    case FullInlining_AA =>
      //try {
        val (newPre, newBody, newPost, vars) = fullInliner.inlineFunctions(c.pre, c.body, c.post)
        val paths = collectPaths(newBody)
        val newInputs = getVariableRecords(newPre)
        val filteredPrecondition = filterPreconditionForBoundsIteration(newPre)
        //println("paths: " + paths.mkString("\n"))
        val apaths = paths.collect {
          case path: Path if (sanityCheck(And(path.condition, filteredPrecondition))) =>
            println("Computing for path: " )//+ path)
            val fullPathCondition = And(path.condition, filteredPrecondition)
            //println("fullPathCondition: " + fullPathCondition)

            val (resConstraint, xfloatMap) =
              if(And(path.expression) == True) { (True, Map[Expr, XFloat]()) }
              else {
                val (xfloats, indices) = xevaluator.evaluate(path.expression, fullPathCondition, newInputs)
                (noiseConstraintFromXFloats(xfloats), xfloats)
                //TODO: see above
                //Noise(ResultVariable(), RationalLiteral(xfloats(ResultVariable()).maxError))
              }
            println("resConstraint: " + resConstraint)
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
      //} catch { case _ => ;}
      //None

      // TODO: postinlining with AA?
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


  private def getPost(c: Constraint, inputs: Map[Variable, Record]): Expr = c.hasFunctionCalls match {
    case false =>
      (findApproximation(c, inputs, List(NoFncs_AA)), c.status) match {
        case (Some(approx), Some(VALID)) =>
          constraintFromResults(Map(ResultVariable() -> approx.actualXfloats(ResultVariable())))
          // TODO: getMostPrecise(c.post, approx.values)
        case (Some(approx), _) => constraintFromResults(Map(ResultVariable() -> approx.actualXfloats(ResultVariable())))
        case (None, Some(VALID)) => c.post
        case (None, _) => True
      }

    case true =>
      (findApproximation(c, inputs, List(FullInlining_AA, FullInlining_AACompactOnFnc)), c.status) match {
        case (Some(approx), Some(VALID)) =>
          constraintFromResults(Map(ResultVariable() -> approx.actualXfloats(ResultVariable())))
          // TODO: getMostPrecise(c.post, approx.values)
        case (Some(approx), _) => constraintFromResults(Map(ResultVariable() -> approx.actualXfloats(ResultVariable())))
        case (None, Some(VALID)) => c.post
        case (None, _) => True
      }
  }

  private def findApproximation(c: Constraint, inputs: Map[Variable, Record], tpes: List[ApproximationType]): Option[ConstraintApproximation] = {
    c.approximations.find(a => tpes.contains(a.tpe)) match {
      case Some(app) => Some(app)
      case None => getNextApproximation(tpes.head, c, inputs)
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
    case Noise(e, f) => BooleanLiteral(true)
    case Roundoff(e) => BooleanLiteral(true)
    case _ => expr
  }

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


  /* def getNextApproximation(tpe: ApproximationType, c: Constraint, inputs: Map[Variable, Record]): Option[ConstraintApproximation] = tpe match {
    /* ******************
       NO APPROXIMATION
    * ******************* */
    case Uninterpreted_None =>
      val paths = collectPaths(c.body).map(p => getAPath(p))
      Some(ConstraintApproximation(c.pre, paths, c.post, Set.empty, tpe))

    case PostInlining_None =>
      postInliner.inlinePostcondition(c.pre, c.body, c.post) match {
        case Some((newPre, newBody, newPost, vars)) =>
          Some(ConstraintApproximation(newPre, collectPaths(newBody).map(p => getAPath(p)), newPost, vars, tpe))
        case None => None
      }

    case FullInlining_None =>
      val (newPre, newBody, newPost, vars) = fullInliner.inlineFunctions(c.pre, c.body, c.post)
      val paths = collectPaths(newBody).map(p => getAPath(p))
      Some(ConstraintApproximation(newPre, paths, newPost, vars, tpe))

    /* ******************
       Full APPROXIMATION
    * ******************* */
    case NoFncs_AA =>
      val (newConstraint, apaths, values) = computeApproxForRes(c.paths, c.pre, inputs)
      Some(ConstraintApproximation(And(c.pre, newConstraint), apaths, c.post, Set.empty, tpe, values))

    case NoFncs_AAPathSensitive =>
      val paths = c.paths
      if (!c.pathsApproximated) for (p <- paths) computeApproximation(p, c.pre, inputs)
      val apaths = paths.collect {
        case p: Path if (p.feasible) => getAPath(p).updateNoisy(True, constraintFromXFloats(p.values))
      }
      Some(ConstraintApproximation(c.pre, apaths, c.post, Set.empty, tpe))

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

    case FullInlining_AA =>
      try {
        val (newPre, newBody, newPost, vars) = fullInliner.inlineFunctions(c.pre, c.body, c.post)
        val (newConstraint, apaths, values) = computeApproxForRes(collectPaths(newBody), newPre, getVariableRecords(newPre))
        return Some(ConstraintApproximation(And(newPre, newConstraint), apaths, newPost, vars, tpe, values))
      } catch { case _ => ;}
      None

      try {
        // TODO: inline pre and post
        // TODO: this overwrites the path.values/indices that may have been computed before
        val paths = c.paths
        for (path <- paths) {
          val pathCondition = And(path.condition, filterPreconditionForBoundsIteration(c.pre))
          val (xfloats, indices) = xevaluator.evaluateWithFncCalls(path.expression, pathCondition, inputs)
          path.values = xfloats
          path.indices = indices
        }
        //val approxValues = mergeRealPathResults(paths)
        //val newConstraint = constraintFromResults(approxValues)
        val apaths = paths.collect {
          case path: Path if (path.feasible) =>
            val resNoise = Noise(ResultVariable(), RationalLiteral(path.values(ResultVariable()).maxError))

            //ideal part, needs fncs inlined
            println("path cond: " + path.condition)
            println("body: " + path.expression)
            val (newPre, newBody, newPost, vars) = fullInliner.inlineFunctions(path.condition, And(path.expression), True)

            println("newPre: " + newPre)
            println("newBody: " + newBody)
            println("newPost: " + newPost)
            APath(newPre,
             True, newBody,
             True, resNoise, path.values)
          }

        return Some(ConstraintApproximation(c.pre, apaths, c.post, Set.empty, tpe))

      } catch { case _=> ;}
      None



    case FullInlining_AAPathSensitive =>
      val (newPre, newBody, newPost, vars) = fullInliner.inlineFunctions(c.pre, c.body, c.post)
      val paths = collectPaths(newBody)
      for (p <- paths) computeApproximation(p, newPre, getVariableRecords(newPre))
      val apaths = paths.collect {
        case p: Path if (p.feasible) => getAPath(p).updateNoisy(True, constraintFromXFloats(p.values))
      }
      Some(ConstraintApproximation(newPre, apaths, newPost, vars, tpe))

    case NoFncs_PartialAA =>
      val paths = c.paths
      if (!c.pathsApproximated) for (p <- paths) computeApproximation(p, c.pre, inputs)

      val apaths = paths.collect {
        case path: Path if (path.feasible) =>
          val approx = path.expression.init.map(eq => eq match {
            case Equals(v, expr) => Noise(v, RationalLiteral(path.values(v).maxError))
            case _ => False
            })

          APath(path.condition,
             path.expression.last, And(path.expression.init),
             path.expression.last, And(approx), path.values)

          /*  //Approximates only the first constraint
          val firstExprConstraint = path.expression.head match {
            case Equals(v @ Variable(id), expr) =>
              //constraintFromXFloats(Map(v -> path.values(v)))
              Noise(v, RationalLiteral(path.values(v).maxError))
            case _ =>
              reporter.error("UUUPS"); False
          }

          APath(path.condition,
             And(path.expression.tail), path.expression.head,
             And(path.expression.tail), firstExprConstraint, path.values)
          */
      }
      Some(ConstraintApproximation(c.pre, apaths, c.post, Set.empty, tpe))


      // TODO: If neither work, do partial approx.
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
