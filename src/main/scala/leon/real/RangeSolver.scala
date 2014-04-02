/* Copyright 2013-2014 EPFL, Lausanne */

package leon
package real

import z3.scala._

import solvers.Solver
import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TypeTrees._
import purescala.TreeOps._

import real.Trees._
import Sat._
import real.TreeOps._
import real.RationalAffineUtils._

// We don't want this to depend on anything Leon internal such as context
class RangeSolver(timeout: Long) {
  var verbose = false

  private[this] var z3: Z3Context = null
  private[this] var freed = false
  //val traceE = new Exception()

  protected[leon] var intSort: Z3Sort = null
  protected[leon] var boolSort: Z3Sort = null
  protected[leon] var realSort: Z3Sort = null
  protected[leon] var exprToZ3Id : Map[Expr,Z3AST] = Map.empty
  protected[leon] var z3IdToExpr : Map[Z3AST,Expr] = Map.empty

  protected[leon] var fallbackSorts: Map[TypeTree, Z3Sort] = Map.empty

  override def finalize() {
    if (!freed) {
      println("!! Solver "+this.getClass.getName+"["+this.hashCode+"] not freed properly prior to GC:")
      //traceE.printStackTrace()
      free()
    }
  }

  def free() {
    freed = true
    if (z3 ne null) {
      z3.delete()
      z3 = null;
    }
  }

  private[this] val z3cfg: Z3Config = new Z3Config(
    "MODEL" -> true,
    "TIMEOUT" -> timeout,
    "TYPE_CHECK" -> true,
    "WELL_SORTED_CHECK" -> true
  )

  private var counter = 0
  private object nextIntForSymbol {
    def apply(): Int = {
      val res = counter
      counter = counter + 1
      res
    }
  }

  var isInitialized = false
  private[this] def initZ3() {
    if (!isInitialized) {
      counter = 0

      z3 = new Z3Context(z3cfg)
      prepareSorts
      isInitialized = true
    }
  }

  initZ3

  val solver = z3.mkSolver

  def assertCnstr(expression: leon.purescala.Trees.Expr): Unit = {
    solver.assertCnstr(toZ3Formula(expression).get)
  }
  
  private def prepareSorts: Unit = {
    intSort = z3.mkIntSort
    boolSort = z3.mkBoolSort
    realSort = z3.mkRealSort
  }

  // assumes prepareSorts has been called....
  protected[leon] def typeToSort(tt: TypeTree): Z3Sort = tt match {
    case Int32Type => intSort
    case BooleanType => boolSort
    case RealType => realSort
    // there is a good bit missing here that we shouldn't need

    case other => fallbackSorts.get(other) match {
      case Some(s) => s
      case None => {
        //reporter.warning("Resorting to uninterpreted type for : " + other)
        println("Resorting to uninterpreted type for : " + other)
        val symbol = z3.mkIntSymbol(nextIntForSymbol())
        val newFBSort = z3.mkUninterpretedSort(symbol)
        fallbackSorts = fallbackSorts + (other -> newFBSort)
        newFBSort
      }
    }
  }

  private[this] def toZ3Formula(expr: Expr, initialMap: Map[Identifier,Z3AST] = Map.empty) : Option[Z3AST] = {
    class CantTranslateException extends Exception

    val varsInformula: Set[Identifier] = variablesOf(expr)

    var z3Vars: Map[Identifier,Z3AST] = if(!initialMap.isEmpty) {
      initialMap
    } else {
      // FIXME TODO pleeeeeeeease make this cleaner. Ie. decide what set of
      // variable has to remain in a map etc.
      exprToZ3Id.filter(p => p._1.isInstanceOf[Variable]).map(p => (p._1.asInstanceOf[Variable].id -> p._2))
    }

    def rec(ex: Expr): Z3AST = { 
      //println("Stacking up call for:")
      //println(ex)
      val recResult = (ex match {
        case Let(i, e, b) => {
          val re = rec(e)
          z3Vars = z3Vars + (i -> re)
          val rb = rec(b)
          z3Vars = z3Vars - i
          rb
        }
        
        case e @ Error(_) => {
          val tpe = e.getType
          val newAST = z3.mkFreshConst("errorValue", typeToSort(tpe))
          exprToZ3Id += (e -> newAST)
          z3IdToExpr += (newAST -> e)
          newAST
        }
        case v @ Variable(id) => z3Vars.get(id) match {
          case Some(ast) => ast
          case None => {
            val newAST = z3.mkFreshConst(id.uniqueName/*name*/, typeToSort(v.getType))
            z3Vars = z3Vars + (id -> newAST)
            exprToZ3Id += (v -> newAST)
            z3IdToExpr += (newAST -> v)
            newAST
          }
        }

        case ite @ IfExpr(c, t, e) => z3.mkITE(rec(c), rec(t), rec(e))
        case And(exs) => z3.mkAnd(exs.map(rec(_)): _*)
        case Or(exs) => z3.mkOr(exs.map(rec(_)): _*)
        case Implies(l, r) => z3.mkImplies(rec(l), rec(r))
        case Iff(l, r) => {
          val rl = rec(l)
          val rr = rec(r)
          z3.mkIff(rl, rr)
        }
        case Not(Iff(l, r)) => z3.mkXor(rec(l), rec(r))
        case Not(Equals(l, r)) => z3.mkDistinct(rec(l), rec(r))
        case Not(e) => z3.mkNot(rec(e))
        case IntLiteral(v) => z3.mkInt(v, intSort)
        case BooleanLiteral(v) => if (v) z3.mkTrue() else z3.mkFalse()
        case RealLiteral(r) =>
          z3.mkNumeral(r.n.toString + "/" + r.d.toString, realSort)
        case Equals(l, r) => z3.mkEq(rec( l ), rec( r ) )
        case Plus(l, r) => z3.mkAdd(rec(l), rec(r))
        case Minus(l, r) => z3.mkSub(rec(l), rec(r))
        case Times(l, r) => z3.mkMul(rec(l), rec(r))
        case Division(l, r) => z3.mkDiv(rec(l), rec(r))
        case Modulo(l, r) => z3.mkMod(rec(l), rec(r))
        case UMinus(e) => z3.mkUnaryMinus(rec(e))
        case PlusR(l, r) => z3.mkAdd(rec(l), rec(r))
        case MinusR(l, r) => z3.mkSub(rec(l), rec(r))
        case TimesR(l, r) => z3.mkMul(rec(l), rec(r))
        case DivisionR(l, r) => z3.mkDiv(rec(l), rec(r))
        case PowerR(l, r) => z3.mkPower(rec(l), rec(r))
        case UMinusR(e) => z3.mkUnaryMinus(rec(e))
        case LessThan(l, r) => z3.mkLT(rec(l), rec(r))
        case LessEquals(l, r) => z3.mkLE(rec(l), rec(r))
        case GreaterThan(l, r) => z3.mkGT(rec(l), rec(r))
        case GreaterEquals(l, r) => z3.mkGE(rec(l), rec(r))
        
        // We only support "simple" expressions for now.
        // For function support use the full Rosa/Leon
        /*case f @ FunctionInvocation(fd, args) => {
          z3.mkApp(functionDefToDecl(fd), args.map(rec(_)): _*)
        }*/
        
        case SetEquals(s1, s2) => z3.mkEq(rec(s1), rec(s2))
        case ElementOfSet(e, s) => z3.mkSetSubset(z3.mkSetAdd(z3.mkEmptySet(typeToSort(e.getType)), rec(e)), rec(s))
        case SubsetOf(s1, s2) => z3.mkSetSubset(rec(s1), rec(s2))
        case SetIntersection(s1, s2) => z3.mkSetIntersect(rec(s1), rec(s2))
        case SetUnion(s1, s2) => z3.mkSetUnion(rec(s1), rec(s2))
        case SetDifference(s1, s2) => z3.mkSetDifference(rec(s1), rec(s2))
        case f @ FiniteSet(elems) => elems.foldLeft(z3.mkEmptySet(typeToSort(f.getType.asInstanceOf[SetType].base)))((ast, el) => z3.mkSetAdd(ast, rec(el)))
        case Distinct(exs) => z3.mkDistinct(exs.map(rec(_)): _*)
  
        case _ => {
          //reporter.warning("Can't handle this in translation to Z3: " + ex + "  " + ex.getClass)
          println("Can't handle this in translation to Z3: " + ex + "  " + ex.getClass)
          throw new CantTranslateException
        }
      })
      recResult
    }

    try {
      val res = Some(rec(expr))

      // if we need to check a constraint with Z3, we need to have the variable declarations
      //z3Vars.values.foreach( v => println("(declare-fun %s () Real)".format(v.toString)))
        
      res
    } catch {
      case e: CantTranslateException => None
    }
  }

  /***
      The Real extension follows here:
  */

  var printWarnings = false
  var diagnose = true
  var countTimeouts = 0
  var countTightRanges = 0
  var countHitPrecisionThreshold = 0
  var countHitIterationThreshold = 0

  def clearCounts = {
    countTimeouts = 0
    countTightRanges = 0
    countHitPrecisionThreshold = 0
    countHitIterationThreshold = 0
  }

  def getCounts: String = "timeouts: %d, tight: %d, hit precision: %d, hit iteration: %d".format(
    countTimeouts, countTightRanges, countHitPrecisionThreshold, countHitIterationThreshold)

  def checkSat(expr: Expr): (Sat, Z3Model) = {
    solver.push
    val variables = variablesOf(expr)
    val cnstr = toZ3Formula(expr)
    //println("\nz3 constraint: " + cnstr)
    solver.assertCnstr(cnstr.get)
    val res: (Sat, Z3Model) = solver.check match {
      case Some(true) =>
        if (verbose) println("--> cond: SAT")
        val model = solver.getModel
        //println("model: " + modelToMap(model, variables))
        (SAT, solver.getModel)
      case Some(false) =>
        if (verbose) println("--> cond: UNSAT")
        (UNSAT, null)
      case None =>
        if (printWarnings) println("!!! WARNING: Z3 SOLVER FAILED")
        countTimeouts = countTimeouts + 1
        (Unknown, null)
    }
    solver.pop()
    res
  }


  def checkValid(expr: Expr): (Option[Boolean], Option[Map[Identifier, Expr]]) = {
    solver.push
    val variables = variablesOf(expr)
    val cnstr = toZ3Formula(Not(expr)).get
    //println("asserting constraint: " + cnstr)
    solver.assertCnstr(cnstr)
    val res = solver.check match {
      case Some(true) =>
        if (verbose) println("--> cond: SAT")
        val model = solver.getModel
        //println("counterexample: " + model)
        //(Some(false), Some(modelToMap(model, variables)))
        (Some(false), None)
      case Some(false) =>
        if (verbose) println("--> cond: UNSAT")
        (Some(true), None)
      case None =>
        if (printWarnings) println("!!! WARNING: Z3 SOLVER FAILED")
        countTimeouts = countTimeouts + 1
        (None, None)
    }
    solver.pop()
    res
  }

  


  def getRange(precond: Expr, expr: Expr, variables: VariablePool, maxIter: Int, prec: Rational) = {
    def inIntervalsWithZ3(expr: Expr, vars: VariablePool): RationalInterval = {
      val tmp = expr match {
        case RealLiteral(r) => RationalInterval(r, r)
        case v @ Variable(_) => vars.getInterval(v)
        case UMinusR(t) => - inIntervalsWithZ3(t, vars)
        case PlusR(l, r) => inIntervalsWithZ3(l, vars) + inIntervalsWithZ3(r, vars)
        case MinusR(l, r) => inIntervalsWithZ3(l, vars) - inIntervalsWithZ3(r, vars)
        case TimesR(l, r) => inIntervalsWithZ3(l, vars) * inIntervalsWithZ3(r, vars)
        case DivisionR(l, r) => inIntervalsWithZ3(l, vars) / inIntervalsWithZ3(r, vars)
        case SqrtR(t) =>
          val tt = inIntervalsWithZ3(t, vars)
          RationalInterval(sqrtDown(tt.xlo), sqrtUp(tt.xhi))
        case PowerR(lhs, IntLiteral(p)) =>
          assert(p > 1, "p is " + p + " in " + expr)
          val lhsInIntervals = inIntervalsWithZ3(lhs, vars)
          var x = lhsInIntervals
          for (i <- 1 until p ){
            x = x * lhsInIntervals
          }
          x
      }
      tightenRange(expr, precond, tmp, maxIter, prec)
    }
    inIntervalsWithZ3(expr, variables)
  }

  def getRangeSimple(precond: Expr, expr: Expr, variables: VariablePool, maxIter: Int, prec: Rational) = {
    def inIntervals(expr: Expr, vars: VariablePool): RationalInterval = expr match {
      case RealLiteral(r) => RationalInterval(r, r)
      case v @ Variable(_) => vars.getInterval(v)
      case UMinusR(t) => - inIntervals(t, vars)
      case PlusR(l, r) => inIntervals(l, vars) + inIntervals(r, vars)
      case MinusR(l, r) => inIntervals(l, vars) - inIntervals(r, vars)
      case TimesR(l, r) => inIntervals(l, vars) * inIntervals(r, vars)
      case DivisionR(l, r) => inIntervals(l, vars) / inIntervals(r, vars)
      case SqrtR(t) =>
        val tt = inIntervals(t, vars)
        RationalInterval(sqrtDown(tt.xlo), sqrtUp(tt.xhi))
      case PowerR(lhs, IntLiteral(p)) =>
        assert(p > 1, "p is " + p + " in " + expr)
        val lhsInIntervals = inIntervals(lhs, vars)
        var x = lhsInIntervals
        for (i <- 1 until p ){
          x = x * lhsInIntervals
        }
        x
    }
    clearCounts
    val approx = inIntervals(expr, variables)
    if(countTimeouts != 0)
      println("\n ******** \nSolver timed out during getRangeSimple computation")
    tightenRange(massageArithmetic(expr), precond, approx, maxIter, prec)
  }

  def tightenRange(tree: Expr, precondition: Expr, initialBound: RationalInterval, maxIter: Int, prec: Rational):
    RationalInterval = tree match {
    case IntLiteral(v) => initialBound
    case RealLiteral(v) => initialBound
    //case Variable(id) => initialBound
    case _ =>
      //println("maxIter: " + maxIter + "    precision: " + prec)
      assert(solver.getNumScopes == 0)
      solver.push
      assertCnstr(precondition)

      val a = initialBound.xlo
      val b = initialBound.xhi
      val exprInZ3 = toZ3Formula(tree).get

      printBoundsResult(checkBounds(exprInZ3, a, b), "initial")

      if (verbose) {
        println("\nComputing range for " + tree)
        println("starting from  [" + a + ", " + b + "]")
        println("\n============Looking for lowerbound")
      }
      // Check if bound is already tight, if so don't bother running Z3 search
      val newLowerBound =
        if (lowerBoundIsTight(exprInZ3, a, prec)) {
          countTightRanges += 1
          a
        } else getLowerBound(a, b, exprInZ3, 0, maxIter, prec)

      if (verbose) println("\n============Looking for upperbound")
      //TODO: start searching from the newLowerBound?
      val newUpperBound =
        if (upperBoundIsTight(exprInZ3, b, prec)) {
          countTightRanges += 1
          b
        }
        else getUpperBound(a, b, exprInZ3, 0, maxIter, prec)

      printBoundsResult(checkBounds(exprInZ3, newLowerBound, newUpperBound), "final")

      solver.pop()
      RationalInterval(newLowerBound, newUpperBound)
  }

  private def checkBounds(tree: Z3AST, lowBound: Rational, upBound: Rational): (Sat, Sat, String) = {
    val resLow = checkLowerBound(tree, lowBound)
    val resUp = checkUpperBound(tree, upBound)
    val diagnoseString = resLow._2 + "\n" + resUp._2
    (resLow._1, resUp._1, diagnoseString)
  }


  private def getLowerBound(a: Rational, b: Rational, exprInZ3: Z3AST, count: Int, maxIter: Int, prec: Rational): Rational = {
    // Enclosure of bound is precise enough
    if (b-a < prec) {
      countHitPrecisionThreshold += 1
      a
    } else if (count > maxIter) {
      countHitIterationThreshold += 1
      a
    } else {
      val mid = a + (b - a) / Rational(2l)
      val res = checkLowerBound(exprInZ3, mid)

      if (verbose) println("checked lwr bound: " + mid + ", with result: " + res)

      res._1 match {
        case SAT => getLowerBound(a, mid, exprInZ3, count + 1, maxIter, prec)
        case UNSAT => getLowerBound(mid, b, exprInZ3, count + 1, maxIter, prec)
        case Unknown => // Return safe answer
          a
      }
    }
  }

  private def getUpperBound(a: Rational, b: Rational, exprInZ3: Z3AST, count: Int, maxIter: Int, prec: Rational): Rational = {
    // Enclosure of bound is precise enough
    if (b-a < prec) {
      countHitPrecisionThreshold += 1
      b
    } else if (count > maxIter) {
      countHitIterationThreshold += 1
      b
    } else {
      val mid = a + (b - a) / Rational(2l)
      val res = checkUpperBound(exprInZ3, mid)

      if (verbose) println("checked upp bound: " + mid + ", with result: " + res)

      res._1 match {
        case SAT => getUpperBound(mid, b, exprInZ3, count + 1, maxIter, prec)
        case UNSAT => getUpperBound(a, mid, exprInZ3, count + 1, maxIter, prec)
        case Unknown => // Return safe answer
          b
      }
    }
  }

  private def checkConstraint: Sat = {
    solver.check match {
      case Some(true) =>
        if (verbose) println("--> bound: SAT")
        SAT
      case Some(false) =>
        if (verbose) println("--> bound: UNSAT")
        UNSAT
      case None =>
        if (printWarnings) println("!!! WARNING: Z3 SOLVER FAILED")
        countTimeouts += 1
        Unknown
    }
  }

  private def checkLowerBound(exprInZ3: Z3AST, bound: Rational): (Sat, String) = {
    var diagnoseString = ""
    solver.push
    solver.assertCnstr(z3.mkLT(exprInZ3, z3.mkNumeral(getNumeralString(bound), realSort)))

    if (verbose) println("checking: " + solver.getAssertions.toSeq.mkString(",\n"))
    if (diagnose) diagnoseString += ("L: checking: " + solver.getAssertions.toSeq.mkString(",\n"))

    val res = checkConstraint
    solver.pop()
    (res, diagnoseString)
  }

  private def checkUpperBound(exprInZ3: Z3AST, bound: Rational): (Sat, String) = {
    var diagnoseString = ""
    solver.push
    solver.assertCnstr(z3.mkGT(exprInZ3, z3.mkNumeral(getNumeralString(bound), realSort)))

    if (verbose) println("checking: " + solver.getAssertions.toSeq.mkString(",\n"))
    if (diagnose) diagnoseString += ("U: checking: " + solver.getAssertions.toSeq.mkString(",\n"))

    val res = checkConstraint
    solver.pop()
    (res, diagnoseString)
  }


  private def lowerBoundIsTight(exprInZ3: Z3AST, bound: Rational, prec: Rational): Boolean = {
    // TODO: uses push and pop, which prevents nlsat to be used, probably
    solver.push
    solver.assertCnstr(z3.mkLT(exprInZ3, z3.mkNumeral(getNumeralString(bound + prec), realSort)))
    if (verbose) println("checking if lower bound is tight: " + solver.getAssertions.toSeq.mkString(",\n"))
    val res = checkConstraint
    solver.pop()
    res match {
      case SAT => true
      case _ => false
    }
  }

  private def upperBoundIsTight(exprInZ3: Z3AST, bound: Rational, prec: Rational): Boolean = {
    solver.push
    solver.assertCnstr(z3.mkGT(exprInZ3, z3.mkNumeral(getNumeralString(bound - prec), realSort)))
    if (verbose) println("checking: " + solver.getAssertions.toSeq.mkString(",\n"))
    val res = checkConstraint
    solver.pop()
    res match {
      case SAT => true
      case _ => false
    }
  }

  private def getNumeralString(r: Rational): String = {
    r.n.toString + "/" + r.d.toString
  }

  // @param which: initial or final
  private def printBoundsResult(res: (Sat, Sat, String), which: String) = res match {
    case (SAT, SAT, msg) =>
      throw new UnsoundBoundsException("!!! ERROR: both " + which + " bounds are not sound!\nmsg: " + msg)
    case (SAT, _, msg) =>
      throw new UnsoundBoundsException("!!! ERROR: " + which + " lower bound is not sound!\nmsg: " + msg)
    case (_, SAT, msg) =>
      throw new UnsoundBoundsException("!!! ERROR: " + which + " upper bound is not sound!\nmsg: " + msg)
    case (UNSAT, UNSAT, msg) =>
      if (verbose) println(which + " bounds check successful.")
    case _ =>
      if (printWarnings || verbose) println("WARNING: cannot check "+which+" bounds.")
  }
}