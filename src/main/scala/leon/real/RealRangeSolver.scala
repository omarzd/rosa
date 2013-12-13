/* Copyright 2013 EPFL, Lausanne */

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


class RealRangeSolver(val context: LeonContext, val program: Program, timeout: Long) extends Solver {
  var verbose = false

  val reporter: Reporter = context.reporter

  // we may not need this, since we don't use interrupts ( I think )
  //context.interruptManager.registerForInterrupts(this)

  def name: String = "Z3-r"

  //var verbose = false
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


  private[this] var freed = false
  val traceE = new Exception()

  override def finalize() {
    if (!freed) {
      println("!! Solver "+this.getClass.getName+"["+this.hashCode+"] not freed properly prior to GC:")
      traceE.printStackTrace()
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

  class CantTranslateException(t: Z3AST) extends Exception("Can't translate from Z3 tree: " + t)

  protected[leon] var intSort: Z3Sort = null
  protected[leon] var boolSort: Z3Sort = null
  protected[leon] var realSort: Z3Sort = null
  //protected[leon] var setSorts: Map[TypeTree, Z3Sort] = Map.empty
  //protected[leon] var mapSorts: Map[TypeTree, Z3Sort] = Map.empty
  //protected[leon] var unitSort: Z3Sort = null
  //protected[leon] var unitValue: Z3AST = null

  protected[leon] var exprToZ3Id : Map[Expr,Z3AST] = Map.empty
  protected[leon] var z3IdToExpr : Map[Z3AST,Expr] = Map.empty

  protected[leon] var fallbackSorts: Map[TypeTree, Z3Sort] = Map.empty

  private[this] val z3cfg: Z3Config = new Z3Config(
    "MODEL" -> true,
    "TIMEOUT" -> timeout,
    "TYPE_CHECK" -> true,
    "WELL_SORTED_CHECK" -> true
  )
  toggleWarningMessages(true)

  private var functionMap: Map[FunDef, Z3FuncDecl] = Map.empty
  private var reverseFunctionMap: Map[Z3FuncDecl, FunDef] = Map.empty
  protected[leon] def prepareFunctions : Unit = {
    functionMap        = Map.empty
    reverseFunctionMap = Map.empty
    for(funDef <- program.definedFunctions) {
      val sortSeq = funDef.args.map(vd => typeToSort(vd.tpe))
      val returnSort = typeToSort(funDef.returnType)

      val z3Decl = z3.mkFreshFuncDecl(funDef.id.name, sortSeq, returnSort)
      functionMap = functionMap + (funDef -> z3Decl)
      reverseFunctionMap = reverseFunctionMap + (z3Decl -> funDef)
    }
  }
  protected[leon] def functionDefToDecl(funDef: FunDef) : Z3FuncDecl = functionMap(funDef)
  protected[leon] def functionDeclToDef(decl: Z3FuncDecl) : FunDef = reverseFunctionMap(decl)
  protected[leon] def isKnownDecl(decl: Z3FuncDecl) : Boolean = reverseFunctionMap.isDefinedAt(decl)

  private[this] var z3: Z3Context = null

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
      //prepareFunctions

      isInitialized = true

      //initTime.stop
      //context.timers.get("Z3Solver init") += initTime
    }
  }

  initZ3

  // not sure we want this
  //val solver = z3.mkSolver

  private var containsFunCalls = false
  
  def assertCnstr(expression: Expr): Unit = ???/*{
    //variables ++= variablesOf(expression)
    containsFunCalls ||= containsFunctionCalls(expression)
    solver.assertCnstr(toZ3Formula(expression).get)
  }*/

  def check: Option[Boolean] = ??? /*{
    solver.check match {
      case Some(true) =>
        if (containsFunCalls) {
          None
        } else {
          Some(true)
        }

      case r =>
        r
    }
  }*/
  
  def getModel: Map[Identifier, Expr] = ???

  // creates a new solver for each check, because we don't want to use an incremental solver
  // nlsat does not work within an incremental solver...
  def checkSat(expr: Expr): (Sat, Z3Model) = {
    val solver = z3.mkSolver
    //solver.push
    val variables = variablesOf(expr)
    //println("check sat of formula: " + expr)
    //println("transformed: " + pushEqualsIntoIfThenElse(expr, None))

    val cnstr = toZ3Formula(pushEqualsIntoIfThenElse(expr, None)).get
    solver.assertCnstr(cnstr)
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
    //solver.pop()
    res
  }

  // Just so we have it
  def getRange(precond: Expr, expr: Expr, variables: VariablePool, maxIter: Int, prec: Rational) = {
    val approx = inIntervals(expr, variables)
    tightenRange(massageArithmetic(expr), precond, approx, maxIter, prec)
  }

  def tightenRange(tree: Expr, precondition: Expr, initialBound: RationalInterval, maxIter: Int, prec: Rational):
    RationalInterval = tree match {
    case IntLiteral(v) => initialBound
    case RealLiteral(v) => initialBound
    //case Variable(id) => initialBound
    case _ =>
      //println("maxIter: " + maxIter + "    precision: " + prec)
      //assert(solver.getNumScopes == 0)
      //solver.push
      //val solver = z3.mkSolver   
      
      //solver.assertCnstr(toZ3Formula(precondition).get)
      val precondInZ3 = toZ3Formula(precondition).get

      val a = initialBound.xlo
      val b = initialBound.xhi
      val exprInZ3 = toZ3Formula(tree).get

      printBoundsResult(checkBounds(precondInZ3, exprInZ3, a, b), "initial")

      if (verbose) {
        println("\nComputing range for " + tree)
        println("starting from  [" + a + ", " + b + "]")
        println("\n============Looking for lowerbound")
      }
      // Check if bound is already tight, if so don't bother running Z3 search
      val newLowerBound =
        if (lowerBoundIsTight(precondInZ3, exprInZ3, a, prec)) {
          countTightRanges += 1
          a
        } else getLowerBound(a, b, precondInZ3, exprInZ3, 0, maxIter, prec)

      if (verbose) println("\n============Looking for upperbound")
      //TODO: we could actually start searching from the newLowerBound, no?
      val newUpperBound =
        if (upperBoundIsTight(precondInZ3, exprInZ3, b, prec)) {
          countTightRanges += 1
          b
        }
        else getUpperBound(a, b, precondInZ3, exprInZ3, 0, maxIter, prec)

      printBoundsResult(checkBounds(precondInZ3, exprInZ3, newLowerBound, newUpperBound), "final")

      //solver.pop()
      RationalInterval(newLowerBound, newUpperBound)
  }

  private def checkBounds(precondInZ3: Z3AST, tree: Z3AST, lowBound: Rational, upBound: Rational): (Sat, Sat, String) = {
    val resLow = checkLowerBound(precondInZ3, tree, lowBound)
    val resUp = checkUpperBound(precondInZ3, tree, upBound)
    val diagnoseString = resLow._2 + "\n" + resUp._2
    (resLow._1, resUp._1, diagnoseString)
  }


  private def getLowerBound(a: Rational, b: Rational, precondInZ3: Z3AST, exprInZ3: Z3AST, count: Int, maxIter: Int, prec: Rational): Rational = {
    // Enclosure of bound is precise enough
    if (b-a < prec) {
      countHitPrecisionThreshold += 1
      return a
    } else if (count > maxIter) {
      countHitIterationThreshold += 1
      return a
    } else {
      val mid = a + (b - a) / Rational(2l)
      val res = checkLowerBound(precondInZ3, exprInZ3, mid)

      if (verbose) println("checked lwr bound: " + mid + ", with result: " + res)

      res._1 match {
        case SAT => getLowerBound(a, mid, precondInZ3, exprInZ3, count + 1, maxIter, prec)
        case UNSAT => getLowerBound(mid, b, precondInZ3, exprInZ3, count + 1, maxIter, prec)
        case Unknown => // Return safe answer
          return a
      }
    }
  }

  private def getUpperBound(a: Rational, b: Rational, precondInZ3: Z3AST, exprInZ3: Z3AST, count: Int, maxIter: Int, prec: Rational): Rational = {
    // Enclosure of bound is precise enough
    if (b-a < prec) {
      countHitPrecisionThreshold += 1
      return b
    } else if (count > maxIter) {
      countHitIterationThreshold += 1
      return b
    } else {
      val mid = a + (b - a) / Rational(2l)
      val res = checkUpperBound(precondInZ3, exprInZ3, mid)

      if (verbose) println("checked upp bound: " + mid + ", with result: " + res)

      res._1 match {
        case SAT => getUpperBound(mid, b, precondInZ3, exprInZ3, count + 1, maxIter, prec)
        case UNSAT => getUpperBound(a, mid, precondInZ3, exprInZ3, count + 1, maxIter, prec)
        case Unknown => // Return safe answer
          return b
      }
    }
  }

  private def checkConstraint(precondInZ3: Z3AST, exprInZ3: Z3AST): Sat = {
    val solver = z3.mkSolver
    solver.assertCnstr(precondInZ3)
    solver.assertCnstr(exprInZ3)
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

  private def checkLowerBound(precondInZ3: Z3AST, exprInZ3: Z3AST, bound: Rational): (Sat, String) = {
    var diagnoseString = ""
    //solver.push
    val cnstr = z3.mkLT(exprInZ3, z3.mkNumeral(getNumeralString(bound), realSort))

    //if (verbose) println("checking: " + solver.getAssertions.toSeq.mkString(",\n"))
    //if (diagnose) diagnoseString += ("L: checking: " + solver.getAssertions.toSeq.mkString(",\n"))

    val res = checkConstraint(precondInZ3, cnstr)
    //solver.pop()
    (res, diagnoseString)
  }

  private def checkUpperBound(precondInZ3: Z3AST, exprInZ3: Z3AST, bound: Rational): (Sat, String) = {
    var diagnoseString = ""
    //solver.push
    val cnstr = z3.mkGT(exprInZ3, z3.mkNumeral(getNumeralString(bound), realSort))

    //if (verbose) println("checking: " + solver.getAssertions.toSeq.mkString(",\n"))
    //if (diagnose) diagnoseString += ("U: checking: " + solver.getAssertions.toSeq.mkString(",\n"))

    val res = checkConstraint(precondInZ3, cnstr)
    //solver.pop()
    (res, diagnoseString)
  }


  private def lowerBoundIsTight(precondInZ3: Z3AST, exprInZ3: Z3AST, bound: Rational, prec: Rational): Boolean = {
    val cnstr = z3.mkLT(exprInZ3, z3.mkNumeral(getNumeralString(bound + prec), realSort))
    //if (verbose) println("checking if lower bound is tight: " + solver.getAssertions.toSeq.mkString(",\n"))
    val res = checkConstraint(precondInZ3, cnstr)
    //solver.pop()
    res match {
      case SAT => true
      case _ => false
    }
  }

  private def upperBoundIsTight(precondInZ3: Z3AST, exprInZ3: Z3AST, bound: Rational, prec: Rational): Boolean = {
    val cnstr = z3.mkGT(exprInZ3, z3.mkNumeral(getNumeralString(bound - prec), realSort))
    //if (verbose) println("checking: " + solver.getAssertions.toSeq.mkString(",\n"))
    val res = checkConstraint(precondInZ3, cnstr)
    //solver.pop()
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
  
  // Prepares some of the Z3 sorts, but *not* the tuple sorts; these are created on-demand.
  private def prepareSorts: Unit = {
    //import Z3Context.{ADTSortReference, RecursiveType, RegularSort}
    
    intSort = z3.mkIntSort
    boolSort = z3.mkBoolSort
    realSort = z3.mkRealSort
    
  }

  // assumes prepareSorts has been called....
  protected[leon] def typeToSort(tt: TypeTree): Z3Sort = tt match {
    case Int32Type => intSort
    case BooleanType => boolSort
    case RealType => realSort
    //case UnitType => unitSort

    // there is a good bit missing here that we shouldn't need

    case other => fallbackSorts.get(other) match {
      case Some(s) => s
      case None => {
        reporter.warning("Resorting to uninterpreted type for : " + other)
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
        /*case tu @ Tuple(args) => {
          // This call is required, because the Z3 sort may not have been generated yet.
          // If it has, it's just a map lookup and instant return.
          typeToSort(tu.getType)
          val constructor = tupleConstructors(tu.getType)
          constructor(args.map(rec(_)): _*)
        }
        case ts @ TupleSelect(tu, i) => {
          // See comment above for similar code.
          typeToSort(tu.getType)
          val selector = tupleSelectors(tu.getType)(i-1)
          selector(rec(tu))
        }*/
        case Let(i, e, b) => {
          val re = rec(e)
          z3Vars = z3Vars + (i -> re)
          val rb = rec(b)
          z3Vars = z3Vars - i
          rb
        }
        // whatever this is?
        //case Waypoint(_, e) => rec(e)
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
            // if (id.isLetBinder) {
            //   scala.sys.error("Error in formula being translated to Z3: identifier " + id + " seems to have escaped its let-definition")
            // }

            // Remove this safety check, since choose() expresions are now
            // translated to non-unrollable variables, that end up here.
            // assert(!this.isInstanceOf[FairZ3Solver], "Trying to convert unknown variable '"+id+"' while using FairZ3")

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
          // z3.mkIff used to trigger a bug
          // z3.mkAnd(z3.mkImplies(rl, rr), z3.mkImplies(rr, rl))
          z3.mkIff(rl, rr)
        }
        case Not(Iff(l, r)) => z3.mkXor(rec(l), rec(r))
        case Not(Equals(l, r)) => z3.mkDistinct(rec(l), rec(r))
        case Not(e) => z3.mkNot(rec(e))
        case IntLiteral(v) => z3.mkInt(v, intSort)
        case BooleanLiteral(v) => if (v) z3.mkTrue() else z3.mkFalse()
        case RealLiteral(r) =>
          z3.mkNumeral(r.n.toString + "/" + r.d.toString, realSort)
        //case UnitLiteral => unitValue
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
        /*case c @ CaseClass(cd, args) => {
          val constructor = adtConstructors(cd)
          constructor(args.map(rec(_)): _*)
        }
        case c @ CaseClassSelector(_, cc, sel) => {
          val selector = adtFieldSelectors(sel)
          selector(rec(cc))
        }
        case c @ CaseClassInstanceOf(ccd, e) => {
          val tester = adtTesters(ccd)
          tester(rec(e))
        }*/
        case f @ FunctionInvocation(fd, args) => {
          z3.mkApp(functionDefToDecl(fd), args.map(rec(_)): _*)
        }
        
        case SetEquals(s1, s2) => z3.mkEq(rec(s1), rec(s2))
        case ElementOfSet(e, s) => z3.mkSetSubset(z3.mkSetAdd(z3.mkEmptySet(typeToSort(e.getType)), rec(e)), rec(s))
        case SubsetOf(s1, s2) => z3.mkSetSubset(rec(s1), rec(s2))
        case SetIntersection(s1, s2) => z3.mkSetIntersect(rec(s1), rec(s2))
        case SetUnion(s1, s2) => z3.mkSetUnion(rec(s1), rec(s2))
        case SetDifference(s1, s2) => z3.mkSetDifference(rec(s1), rec(s2))
        case f @ FiniteSet(elems) => elems.foldLeft(z3.mkEmptySet(typeToSort(f.getType.asInstanceOf[SetType].base)))((ast, el) => z3.mkSetAdd(ast, rec(el)))
        /*case SetCardinality(s) => {
          val rs = rec(s)
          setCardFuns(s.getType.asInstanceOf[SetType].base)(rs)
        }
        case SetMin(s) => intSetMinFun(rec(s))
        case SetMax(s) => intSetMaxFun(rec(s))
        case f @ FiniteMap(elems) => f.getType match {
          case tpe@MapType(fromType, toType) =>
            typeToSort(tpe) //had to add this here because the mapRangeNoneConstructors was not yet constructed...
            val fromSort = typeToSort(fromType)
            val toSort = typeToSort(toType)
            elems.foldLeft(z3.mkConstArray(fromSort, mapRangeNoneConstructors(toType)())){ case (ast, (k,v)) => z3.mkStore(ast, rec(k), mapRangeSomeConstructors(toType)(rec(v))) }
          case errorType => scala.sys.error("Unexpected type for finite map: " + (ex, errorType))
        }
        case mg @ MapGet(m,k) => m.getType match {
          case MapType(fromType, toType) =>
            val selected = z3.mkSelect(rec(m), rec(k))
            mapRangeValueSelectors(toType)(selected)
          case errorType => scala.sys.error("Unexpected type for map: " + (ex, errorType))
        }
        case MapUnion(m1,m2) => m1.getType match {
          case MapType(ft, tt) => m2 match {
            case FiniteMap(ss) =>
              ss.foldLeft(rec(m1)){
                case (ast, (k, v)) => z3.mkStore(ast, rec(k), mapRangeSomeConstructors(tt)(rec(v)))
              }
            case _ => scala.sys.error("map updates can only be applied with concrete map instances")
          }
          case errorType => scala.sys.error("Unexpected type for map: " + (ex, errorType))
        }
        case MapIsDefinedAt(m,k) => m.getType match {
          case MapType(ft, tt) => z3.mkDistinct(z3.mkSelect(rec(m), rec(k)), mapRangeNoneConstructors(tt)())
          case errorType => scala.sys.error("Unexpected type for map: " + (ex, errorType))
        }
        case fill @ ArrayFill(length, default) => {
          val at@ArrayType(base) = fill.getType
          typeToSort(at)
          val cons = arrayTupleCons(at)
          val ar = z3.mkConstArray(typeToSort(base), rec(default))
          val res = cons(ar, rec(length))
          res
        }
        case ArraySelect(a, index) => {
          typeToSort(a.getType)
          val ar = rec(a)
          val getArray = arrayTupleSelectorArray(a.getType)
          val res = z3.mkSelect(getArray(ar), rec(index))
          res
        }
        case ArrayUpdated(a, index, newVal) => {
          typeToSort(a.getType)
          val ar = rec(a)
          val getArray = arrayTupleSelectorArray(a.getType)
          val getLength = arrayTupleSelectorLength(a.getType)
          val cons = arrayTupleCons(a.getType)
          val store = z3.mkStore(getArray(ar), rec(index), rec(newVal))
          val res = cons(store, getLength(ar))
          res
        }
        case ArrayLength(a) => {
          typeToSort(a.getType)
          val ar = rec(a)
          val getLength = arrayTupleSelectorLength(a.getType)
          val res = getLength(ar)
          res
        }

        case arr @ FiniteArray(exprs) => {
          val ArrayType(innerType) = arr.getType
          val arrayType = arr.getType
          val a: Expr = ArrayFill(IntLiteral(exprs.length), simplestValue(innerType)).setType(arrayType)
          val u = exprs.zipWithIndex.foldLeft(a)((array, expI) => ArrayUpdated(array, IntLiteral(expI._2), expI._1).setType(arrayType))
          rec(u)
        }*/
        case Distinct(exs) => z3.mkDistinct(exs.map(rec(_)): _*)
  
        case _ => {
          reporter.warning("Can't handle this in translation to Z3: " + ex + "  " + ex.getClass)
          throw new CantTranslateException
        }
      })
      recResult
    }

    try {
      val res = Some(rec(expr))
      res
    } catch {
      case e: CantTranslateException => None
    }
  }

}