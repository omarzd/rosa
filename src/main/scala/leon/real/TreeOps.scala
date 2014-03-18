/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import purescala.TransformerWithPC
import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._

import xlang.Trees._
import real.Trees._
import real.RationalAffineUtils._
import VCKind._
import VariableShop._
import real.{FixedPointFormat => FPFormat}

object TreeOps {

  def letsToEquals(expr: Expr): Expr = expr match {
    case Equals(l, r) => Equals(l, letsToEquals(r))
    case IfExpr(cond, thenn, elze) =>
      IfExpr(cond, letsToEquals(thenn), letsToEquals(elze))

    case Let(binder, value, body) =>
      And(Equals(Variable(binder), letsToEquals(value)), letsToEquals(body))

    case Block(exprs, last) =>
      And(exprs.map(e => letsToEquals(e)) :+ letsToEquals(last))

    case _ => expr
  }

  def containsIfExpr(expr: Expr): Boolean = {
    exists{
      case _: IfExpr => true
      case _ => false
    }(expr)
  }

  /* ----------------------
         Analysis phase
   ------------------------ */
  def addResults(expr: Expr, variables: Seq[Expr]): Expr = expr match {
    case Equals(v, IfExpr(c, t, e)) =>
      IfExpr(c, addResults(t, Seq(v)), addResults(e, Seq(v)))

    case Equals(_,_) => expr

    case IfExpr(c, t, e) =>
      IfExpr(c, addResults(t, variables), addResults(e, variables))

    case LessEquals(_, _) | LessThan(_,_) | GreaterThan(_,_) | GreaterEquals(_,_) => expr

    case And(ands) => And(ands.map( addResults(_, variables)))
    case Or(ors) => Or(ors.map(addResults(_, variables)))

    case UMinusR(_) | PlusR(_, _) | MinusR(_, _) | TimesR(_, _) | DivisionR(_, _) | SqrtR(_) | Variable(_) =>
      Equals(variables.head, expr)

    case BooleanLiteral(_) => expr

    case Noise(_,_) => expr

    case Tuple(bases) =>
      assert(bases.length == variables.length)
      And(variables.zip(bases).map({
        case (resVar, tplPart) => Equals(resVar, tplPart)
        }))

    case Not(t) => Not(addResults(t, variables))

    case FncValue(specs, specExpr) =>
      assert(specs.length == variables.length)
      And(variables.zip(specs).map({
        case (resVar, spec) =>
          And(specToExpr(spec), Equals(resVar, Variable(spec.id)))
        }))
    
    // TODO: this won't work with tuples
    //case FunctionInvocation(_, _) => Equals(variables.head, expr)
  }

  def addResultsF(expr: Expr, variables: Seq[Expr]): Expr = expr match {
    case EqualsF(v, FloatIfExpr(c, t, e)) =>
      FloatIfExpr(c, addResultsF(t, Seq(v)), addResultsF(e, Seq(v)))

    case EqualsF(_,_) => expr

    case FloatIfExpr(c, t, e) =>
      FloatIfExpr(c, addResultsF(t, variables), addResultsF(e, variables))

    case LessEquals(_, _) | LessThan(_,_) | GreaterThan(_,_) | GreaterEquals(_,_) => expr

    case And(ands) => And(ands.map( addResultsF(_, variables)))
    case Or(ors) => Or(ors.map(addResultsF(_, variables)))

    case UMinusF(_) | PlusF(_, _) | MinusF(_, _) | TimesF(_, _) | DivisionF(_, _) | SqrtF(_) | Variable(_) =>
      EqualsF(variables.head, expr)

    case BooleanLiteral(_) => expr

    case Noise(_,_) => expr

    case Tuple(bases) =>
      assert(bases.length == variables.length)
      And(variables.zip(bases).map({
        case (resVar, tplPart) => EqualsF(resVar, tplPart)
        }))

    case Not(t) => Not(addResultsF(t, variables))

    case FncValue(specs, specExpr) =>
      assert(specs.length == variables.length)
      And(variables.zip(specs).map({
        case (resVar, spec) =>
          And(specToExpr(spec), EqualsF(resVar, Variable(spec.id)))
        }))
    
    // TODO: this won't work with tuples
    //case FunctionInvocationF(_, _) => EqualsF(variable.get, expr)
  }

  /* -----------------------
             Paths
   ------------------------- */
  def getPaths(expr: Expr): Set[(Expr, Expr)] = {
    collectPaths(expr).map(p => (p.condition, And(p.expression)))
  }

  case class PartialPath(condition: Expr, expression: Seq[Expr]) {
    def addCondition(c: Expr): PartialPath =
      PartialPath(And(condition, c), expression)

    def addPath(p: PartialPath): PartialPath = {
      PartialPath(And(this.condition, p.condition), this.expression ++ p.expression)
    }

    def addEqualsToLast(e: Expr): PartialPath = {
      PartialPath(condition, expression.init ++ List(Equals(e, expression.last)))
    }
  }

  def collectPaths(expr: Expr): Set[PartialPath] = expr match {
    case IfExpr(cond, thenn, elze) =>
      val thenPaths = collectPaths(thenn).map(p => p.addCondition(cond))
      val elzePaths = collectPaths(elze).map(p => p.addCondition(negate(cond)))

      thenPaths ++ elzePaths

    case And(args) =>
      var currentPaths: Set[PartialPath] = collectPaths(args.head)

      for (a <- args.tail) {
        var newPaths: Set[PartialPath] = Set.empty
        val nextPaths = collectPaths(a)

        for (np <- nextPaths; cp <- currentPaths)
          newPaths = newPaths + cp.addPath(np)

        currentPaths = newPaths
      }
      currentPaths

    case Equals(e, f) =>
      collectPaths(f).map(p => p.addEqualsToLast(e))

    case _ =>
      Set(PartialPath(True, List(expr)))
  }


  /* -----------------------
           Evaluation
   ------------------------- */
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
  }




  /* -----------------------
        Function calls
   ------------------------- */
  class AssertionCollector(outerFunDef: FunDef, precondition: Expr, variables: VariablePool, precisions: List[Precision]) extends TransformerWithPC {
    type C = Seq[Expr]
    val initC = Nil

    var vcs = Seq[VerificationCondition]()

    def register(e: Expr, path: C) = path :+ e

    override def rec(e: Expr, path: C) = e match {
      case FunctionInvocation(funDef, args) if (funDef.precondition.isDefined) =>

        val (simpleArgs, morePath) = args.map(a => a match {
          case Variable(_) => (a, True)
          case _ =>
            val fresh = getFreshTmp
            (fresh, Equals(fresh, a))
        }).unzip

        val pathToFncCall = And(path ++ morePath)
        val arguments: Map[Expr, Expr] = funDef.params.map(decl => decl.toVariable).zip(simpleArgs).toMap
        val toProve = replace(arguments, removeRoundoff(funDef.precondition.get))

        val allFncCalls = functionCallsOf(pathToFncCall).map(invc => invc.tfd.id.toString)
        vcs :+= new VerificationCondition(outerFunDef, Precondition, precondition, pathToFncCall, toProve, allFncCalls, variables, precisions)
        e

      case Assertion(toProve) =>
        val pathToAssertion = And(path)
        val allFncCalls = functionCallsOf(pathToAssertion).map(invc => invc.tfd.id.toString)
        vcs :+= new VerificationCondition(outerFunDef, Assert, precondition, pathToAssertion, toProve, allFncCalls, variables, precisions)
        e
      case _ =>
        super.rec(e, path)
    }
  }

  def extractPostCondition(resId: Identifier, postExpr: Expr, resFresh: Seq[Identifier]): Expr = postExpr match {
    case MatchExpr(Variable(scrutinee),
      Seq(SimpleCase(TuplePattern(None, wildcards), caseExpr))) if (scrutinee == resId) =>
      val replaceMap: Map[Expr, Expr] = wildcards.map({
        case WildcardPattern(Some(id)) => Variable(id)
        case _ => throw new Exception("Unsupported match expression"); null
        }).zip(resFresh.map(Variable(_))).toMap
      
      replace(replaceMap, caseExpr)
     
    case m: MatchExpr =>
      throw new Exception("! Wrong use of match expression for postcondition !")
      null

    case _ => // simple case (no tuples)
      replace(Map(Variable(resId) -> Variable(resFresh.head)), postExpr)
  }

  /*
    Replace the function call with its specification. For translation to Z3 FncValue needs to be translated
    with a fresh variable. For approximation, translate the spec into an XFloat.
  */
  def inlinePostcondition(expr: Expr, precision: Precision, postMap: Map[FunDef, Seq[Spec]]): Expr = {
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
            println(s"$resFresh")
            val postcondition = extractPostCondition(resId, postExpr, resFresh)
            println(s"$postcondition")

            try {
              val specs: Seq[Spec] = resFresh.map( r => {
                extractSpecs(postcondition, r).get
              })
              val deltaMap: Map[Identifier, Rational] = specs.map( s => (s.id, s.absError)).toMap

              val realSpecExpr = actualToRealSpec(postcondition, deltaMap)

              Some(FncValue(specs, replace(arguments, realSpecExpr)))
            } catch {
              case e: Exception => None
            }
        }) match {
          case Some(fncValue) => Some(fncValue)
          case _ => postMap.getOrElse(funDef, Seq()) match {
            case specs: Seq[Spec] if specs.nonEmpty =>
              val specsExpr = And(specs.map(specToExpr(_)))
              Some(FncValue(specs, replace(arguments, specsExpr)))
            case _ =>
              throw PostconditionInliningFailedException("missing postcondition for " + funDef.id.name);
              null
          }
        }

      case _ => None
    }(expr)
  }


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
        throw new Exception("found integer arithmetic in ResultCollector")

      case _ => ;
    } (e)

    error flatMap ( err => {
        if ((lwrBoundReal.nonEmpty || lwrBoundActual.nonEmpty) && (upBoundReal.nonEmpty || upBoundActual.nonEmpty)) {
          Some(Spec(id, RationalInterval(lwrBoundReal.getOrElse(lwrBoundActual.get - err),
               upBoundReal.getOrElse(upBoundActual.get + err)), err))
        } else {
          None
        }
      })
  }

  def actualToRealSpec(e: Expr, deltas: Map[Identifier, Rational]): Expr = {
    val ids = deltas.keys.toSeq

    preMap {
      case LessEquals(RealLiteral(lwrBnd), Actual(Variable(id))) if (ids.contains(id)) =>
        Some(LessEquals(RealLiteral(lwrBnd - deltas(id)), Variable(id)))

      case LessEquals(Actual(Variable(id)), RealLiteral(uprBnd)) if (ids.contains(id)) =>
        Some(LessEquals(Variable(id), RealLiteral(uprBnd + deltas(id))))

      case LessThan(RealLiteral(lwrBnd), Actual(Variable(id))) if (ids.contains(id)) =>
        Some(LessThan(RealLiteral(lwrBnd - deltas(id)), Variable(id)))

      case LessThan(Actual(Variable(id)), RealLiteral(uprBnd)) if (ids.contains(id)) =>
        Some(LessThan(Variable(id), RealLiteral(uprBnd + deltas(id))))

      case GreaterEquals(RealLiteral(uprBnd), Actual(Variable(id))) if (ids.contains(id)) =>
        Some(GreaterEquals(RealLiteral(uprBnd + deltas(id)), Variable(id)))

      case GreaterEquals(Actual(Variable(id)), RealLiteral(lwrBnd)) if (ids.contains(id)) =>
        Some(GreaterEquals(Variable(id), RealLiteral(lwrBnd - deltas(id))))

      case GreaterThan(RealLiteral(uprBnd), Actual(Variable(id))) if (ids.contains(id)) =>
        Some(GreaterThan(RealLiteral(uprBnd + deltas(id)), Variable(id)))

      case GreaterThan(Actual(Variable(id)), RealLiteral(lwrBnd)) if (ids.contains(id)) =>
        Some(GreaterThan(Variable(id), RealLiteral(lwrBnd - deltas(id))))

      case _ => None
    }(e)
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

  /* -----------------------
       Fixed-points
   ------------------------- */

  def toSSA(expr: Expr, fncs: Map[FunDef, Fnc]): Expr = {
    val transformer = new SSATransformer(fncs)
    transformer.transform(expr)
  }

  private class SSATransformer(fncs: Map[FunDef, Fnc]) extends TransformerWithPC {
    type C = Seq[Expr]
    val initC = Nil

    // Note that this transforms real arithmetic to float arithmetic
    private def arithToSSA(expr: Expr): (Seq[Expr], Expr) = expr match {
      case PlusR(lhs, rhs) =>
        val (lSeq, lVar) = arithToSSA(lhs)
        val (rSeq, rVar) = arithToSSA(rhs)
        val tmpVar = getFreshValidTmp
        (lSeq ++ rSeq :+ Equals(tmpVar, PlusR(lVar, rVar)), tmpVar)

      case MinusR(lhs, rhs) =>
        val (lSeq, lVar) = arithToSSA(lhs)
        val (rSeq, rVar) = arithToSSA(rhs)
        val tmpVar = getFreshValidTmp
        (lSeq ++ rSeq :+ Equals(tmpVar, MinusR(lVar, rVar)), tmpVar)

      case TimesR(lhs, rhs) =>
        val (lSeq, lVar) = arithToSSA(lhs)
        val (rSeq, rVar) = arithToSSA(rhs)
        val tmpVar = getFreshValidTmp
        (lSeq ++ rSeq :+ Equals(tmpVar, TimesR(lVar, rVar)), tmpVar)

      case DivisionR(lhs, rhs) =>
        val (lSeq, lVar) = arithToSSA(lhs)
        val (rSeq, rVar) = arithToSSA(rhs)
        val tmpVar = getFreshValidTmp
        (lSeq ++ rSeq :+ Equals(tmpVar, DivisionR(lVar, rVar)), tmpVar)

      case UMinusR(t) =>
        val (seq, v) = arithToSSA(t)
        val tmpVar = getFreshValidTmp
        (seq :+ Equals(tmpVar, UMinusR(v)), tmpVar)

      case RealLiteral(_) | Variable(_) => (Seq[Expr](), expr)

      case FunctionInvocation(funDef, args) =>
        val argsToSSA: Seq[(Seq[Expr], Expr)] = args.map( arithToSSA(_) )

        val (ssa, newArgs) = argsToSSA.unzip

        val arguments: Map[Expr, Expr] = funDef.fd.params.map(decl => decl.toVariable).zip(newArgs).toMap
        val fncBody = fncs(funDef.fd).body

        val newBody = replace(arguments, fncBody)
        
        val tmpVar = getFreshValidTmp
        (ssa.flatten :+ Equals(tmpVar, FncBody(funDef.id.name, newBody, funDef.fd, newArgs)), tmpVar)

    }

    def register(e: Expr, path: C) = path :+ e

    override def rec(e: Expr, path: C) = e match {
      case Equals(v, arithExpr: RealArithmetic) =>
        val (seq, tmpVar) = arithToSSA(arithExpr)
        And(And(seq), EqualsF(v, tmpVar))

      case Equals(v, fnc: FunctionInvocation) =>
        val (seq, tmpVar) = arithToSSA(fnc)
        And(And(seq), EqualsF(v, tmpVar))
      
      case IfExpr(GreaterEquals(l, r), t, e) =>
        val (seqLhs, tmpVarLhs) = arithToSSA(l)
        val (seqRhs, tmpVarRhs) = arithToSSA(r)
        And(And(seqLhs ++ seqRhs), IfExpr(GreaterEquals(tmpVarLhs, tmpVarRhs), rec(t, path), rec(e, path)))

      case IfExpr(LessEquals(l, r), t, e) =>
        val (seqLhs, tmpVarLhs) = arithToSSA(l)
        val (seqRhs, tmpVarRhs) = arithToSSA(r)
        And(And(seqLhs ++ seqRhs), IfExpr(LessEquals(tmpVarLhs, tmpVarRhs), rec(t, path), rec(e, path)))

      case IfExpr(GreaterThan(l, r), t, e) =>
        val (seqLhs, tmpVarLhs) = arithToSSA(l)
        val (seqRhs, tmpVarRhs) = arithToSSA(r)
        And(And(seqLhs ++ seqRhs), IfExpr(GreaterThan(tmpVarLhs, tmpVarRhs), rec(t, path), rec(e, path)))

      case IfExpr(LessThan(l, r), t, e) =>
        val (seqLhs, tmpVarLhs) = arithToSSA(l)
        val (seqRhs, tmpVarRhs) = arithToSSA(r)
        And(And(seqLhs ++ seqRhs), IfExpr(LessThan(tmpVarLhs, tmpVarRhs), rec(t, path), rec(e, path)))

      case arithExpr: RealArithmetic =>
        val (seq, tmpVar) = arithToSSA(arithExpr)
        And(And(seq), tmpVar)

      case fnc: FunctionInvocation =>
        val (seq, tmpVar) = arithToSSA(fnc)
        And(And(seq), tmpVar)

      case _ =>
        super.rec(e, path)
    }
  }

  /**
    Removes all error terms.
  */
  def removeErrors(e: Expr): Expr = {
    preMap {
      case Noise(_,_) | Roundoff(_) | RelError(_,_) => Some(True)
      case _ => None
    }(e)
  }

  /**
    Removes only Roundoff() terms.
  */
  def removeRoundoff(e: Expr): Expr = {
    preMap {
      case Roundoff(_) => Some(True)
      case _ => None
    }(e) 
  }

  /**
    Removes all errors and replaces ~x with x.
  */
  def removeErrorsAndActual(e: Expr): Expr = {
    preMap {
      case Noise(_,_) | Roundoff(_) | RelError(_,_) => Some(True)
      case Actual(e) => Some(e)
      case _ => None
    }(e)
  }

  def idealToActual(expr: Expr, vars: VariablePool): Expr = {
    val transformer = new RealToFloatTransformer(vars)
    transformer.transform(expr)
  }

  private class RealToFloatTransformer(variables: VariablePool) extends TransformerWithPC {
    type C = Seq[Expr]
    val initC = Nil

    def register(e: Expr, path: C) = path :+ e

    // (Sound) Overapproximation in the case of strict inequalities
    override def rec(e: Expr, path: C) = e match {
      case UMinusR(t) => UMinusF(rec(t, path))
      case PlusR(lhs, rhs) => PlusF(rec(lhs, path), rec(rhs, path))
      case MinusR(lhs, rhs) => MinusF(rec(lhs, path), rec(rhs, path))
      case TimesR(lhs, rhs) => TimesF(rec(lhs, path), rec(rhs, path))
      case DivisionR(lhs, rhs) => DivisionF(rec(lhs, path), rec(rhs, path))
      case SqrtR(t) => SqrtF(rec(t, path))
      case v: Variable => variables.buddy(v)
      //case ResultVariable() => FResVariable()
      case RealLiteral(r) => new FloatLiteral(r)
      case IfExpr(cond, thenn, elze) => FloatIfExpr(rec(cond, path), rec(thenn, path), rec(elze, path))
      case Equals(l, r) => EqualsF(rec(l, path), rec(r, path))
      // leave conditions on if-then-else in reals, as they will be passed as conditions to Z3
      case LessEquals(_,_) | LessThan(_,_) | GreaterEquals(_,_) | GreaterThan(_,_) => e

      case FncValue(s, id) => FncValueF(s, id)
      case FncBody(n, b, f, a) => FncBodyF(n, rec(b, path), f, a)
      case FunctionInvocation(fundef, args) =>
        FncInvocationF(fundef, args.map(a => rec(a, path)))

      case Times(_, _) | Plus(_, _) | Division(_, _) | Minus(_, _) | UMinus(_) =>
        throw new Exception("found integer arithmetic in RealToFloatTransformer")
        null
      case _ =>
        super.rec(e, path)
    }
  }

  def specToExpr(s: Spec): Expr = {
    And(And(LessEquals(RealLiteral(s.bounds.xlo), Variable(s.id)),
            LessEquals(Variable(s.id), RealLiteral(s.bounds.xhi))),
            Noise(Variable(s.id), RealLiteral(s.absError)))
  }

  def specToRealExpr(spec: Spec): Expr =
    And(LessEquals(RealLiteral(spec.bounds.xlo), Variable(spec.id)),
            LessEquals(Variable(spec.id), RealLiteral(spec.bounds.xhi)))

  /* --------------------
        Arithmetic ops
   ---------------------- */
  
  def massageArithmetic(expr: Expr): Expr = {
    //TODO: remove redundant definitions of errors? stuff like And(Or(idealPart), Or(actualPart))
    val t1 = distributeMinus(expr)
    //println("t1: " + t1.getClass)
    val t2 = factorize(factorize(t1))
    //println("t2: " + t2)
    val t3 = collectProducts(t2)
    //println("t3: " + t3)
    val t4 = transformPowers(t3)
    //println("t4: " + t4)
    simplifyArithmetic(t4)
  }


  def collectPowers(expr: Expr): Expr = {
    val t2 = collectProducts(expr)
    val t3 = transformPowers(t2)
    t3
  }

  def collectProducts(e: Expr): Expr = {
    postMap{
      case TimesR(l, r) => Some(Product(l, r))
      case _ => None
    }(e)
  }

  def transformPowers(e: Expr): Expr = {
    preMap {
      case Product(exprs) =>
        val groups: Map[String, Seq[Expr]] = exprs.groupBy[String]( expr => expr.toString )
        val groupsRec = groups.map( x =>
          if (x._2.size == 1) {
            x._2.head
          } else {
            PowerR(x._2.head, IntLiteral(x._2.size))
          }
        )

        Some(groupsRec.tail.foldLeft[Expr](groupsRec.head)((x, y) => TimesR(x, y)))

      case _ => None
    }(e)
  }

  def factorize(e: Expr): Expr = {
    preMap {
      case TimesR(f, PlusR(a, b)) => Some(PlusR(TimesR(f, a), TimesR(f, b)))
      case TimesR(PlusR(a, b), f) => Some(PlusR(TimesR(a, f), TimesR(b, f)))
      case TimesR(f, MinusR(a, b)) => Some(MinusR(TimesR(f, a), TimesR(f, b)))
      case TimesR(MinusR(a, b), f) => Some(MinusR(TimesR(a, f), TimesR(b, f)))
      case Times(_, _) | Plus(_, _) | Division(_, _) | Minus(_, _) | UMinus(_) =>
        throw new Exception("found integer arithmetic in Factorizer")
        null
      case _ => None
    }(e)
  }

  def distributeMinus(e: Expr): Expr = {
    preMap {
      case UMinusR(PlusR(x, y)) => Some(MinusR(UMinusR(x), y))
      case UMinusR(MinusR(x, y)) => Some(PlusR(UMinusR(x), y))
      case UMinusR(TimesR(x, y)) => Some(TimesR(UMinusR(x), y))
      case UMinusR(DivisionR(x, y)) => Some(DivisionR(UMinusR(x), y))
      case UMinusR(UMinusR(x)) => Some(x)
      case Times(_, _) | Plus(_, _) | Division(_, _) | Minus(_, _) | UMinus(_) =>
        throw new Exception("found integer arithmetic in MinusDistributor " + e)
        null
      case _ => None
    }(e)
  }

   // Copied from purescala.TreeOps, added RealLiteral
  def simplifyArithmetic(expr: Expr): Expr = {
    def simplify0(expr: Expr): Expr = expr match {
      case PlusR(RealLiteral(i1), RealLiteral(i2)) => RealLiteral(i1 + i2)
      case PlusR(RealLiteral(z), e) if (z == Rational.zero) => e
      case PlusR(e, RealLiteral(z)) if (z == Rational.zero) => e
      case PlusR(PlusR(e, RealLiteral(i1)), RealLiteral(i2)) => PlusR(e, RealLiteral(i1+i2))
      case PlusR(PlusR(RealLiteral(i1), e), RealLiteral(i2)) => PlusR(RealLiteral(i1+i2), e)

      case MinusR(e, RealLiteral(z)) if (z == Rational.zero) => e
      case MinusR(RealLiteral(z), e) if (z == Rational.zero) => UMinusR(e)
      case MinusR(RealLiteral(i1), RealLiteral(i2)) => RealLiteral(i1 - i2)
      case UMinusR(RealLiteral(x)) => RealLiteral(-x)

      case MinusR(e1, UMinusR(e2)) => PlusR(e1, e2)
      case MinusR(e1, MinusR(UMinusR(e2), e3)) => PlusR(e1, PlusR(e2, e3))
      case UMinusR(UMinusR(x)) => x
      case UMinusR(PlusR(UMinusR(e1), e2)) => PlusR(e1, UMinusR(e2))
      case UMinusR(MinusR(e1, e2)) => MinusR(e2, e1)

      case TimesR(RealLiteral(i1), RealLiteral(i2)) => RealLiteral(i1 * i2)
      case TimesR(RealLiteral(o), e) if (o == Rational.one) => e
      case TimesR(RealLiteral(no), e) if (no == -Rational.one) => UMinusR(e)
      case TimesR(e, RealLiteral(o)) if (o == Rational.one) => e
      case TimesR(RealLiteral(z), _) if (z == Rational.zero) => RealLiteral(Rational.zero)
      case TimesR(_, RealLiteral(z)) if (z == Rational.zero) => RealLiteral(Rational.zero)
      case TimesR(RealLiteral(i1), TimesR(RealLiteral(i2), t)) => TimesR(RealLiteral(i1*i2), t)
      case TimesR(RealLiteral(i1), TimesR(t, RealLiteral(i2))) => TimesR(RealLiteral(i1*i2), t)
      case TimesR(RealLiteral(i), UMinusR(e)) => TimesR(RealLiteral(-i), e)
      case TimesR(UMinusR(e), RealLiteral(i)) => TimesR(e, RealLiteral(-i))

      case DivisionR(RealLiteral(i1), RealLiteral(i2)) if i2 != 0 => RealLiteral(i1 / i2)
      case DivisionR(e, RealLiteral(o)) if (o == Rational.one) => e

      case PowerR(RealLiteral(o), e) if (o == Rational.one) => RealLiteral(Rational.one)

      //here we put more expensive rules
      //btw, I know those are not the most general rules, but they lead to good optimizations :)
      case PlusR(UMinusR(PlusR(e1, e2)), e3) if e1 == e3 => UMinusR(e2)
      case PlusR(UMinusR(PlusR(e1, e2)), e3) if e2 == e3 => UMinusR(e1)
      case MinusR(e1, e2) if e1 == e2 => RealLiteral(Rational.zero)
      case MinusR(PlusR(e1, e2), PlusR(e3, e4)) if e1 == e4 && e2 == e3 => RealLiteral(Rational.zero)
      case MinusR(PlusR(e1, e2), PlusR(PlusR(e3, e4), e5)) if e1 == e4 && e2 == e3 => UMinusR(e5)
      case Times(_, _) | Plus(_, _) | Division(_, _) | Minus(_, _) | UMinus(_) =>
        throw new Exception("found integer arithmetic in simplifyArithmetic")
        null
      //default
      case e => e
    }
    def fix[A](f: (A) => A)(a: A): A = {
      val na = f(a)
      if(a == na) a else fix(f)(na)
    }


    val res = fix(simplePostTransform(simplify0))(expr)
    res
  } // end simplify arithmetic

  def actualToIdealVars(e: Expr, variables: VariablePool) = {
    preMap {
      case v @ Variable(_) =>
        variables.getIdealOrNone(v) match {
          case Some(ideal) => Some(ideal)
          case None => Some(v)
        }
      case _ => None
    }(e)
  }

  // Accepts SSA format only and transforms actual to ideal
  def translateToFP(expr: Expr, formats: Map[Expr, FPFormat], bitlength: Int, getConstant: (Rational, Int) => Expr): Expr = expr match {
    case And(exprs) =>
      And(exprs.map(e => translateToFP(e, formats, bitlength, getConstant)))

    case FloatIfExpr(c, t, e) =>
      IfExpr(translateToFP(c, formats, bitlength, getConstant), translateToFP(t, formats, bitlength, getConstant),
                  translateToFP(e, formats, bitlength, getConstant))

    case GreaterEquals(_, _) | GreaterThan(_, _) | LessEquals(_, _) | LessThan(_, _) => expr

    case FncBodyF(name, body, funDef, args) =>
      FunctionInvocation(TypedFunDef(funDef, Seq.empty), args) 

    case EqualsF(vr, PlusF(lhs, rhs)) =>
      val resultFormat = formats(vr)
      val mx = resultFormat.f
      val (ll, rr, mr) = alignOperators(lhs, rhs, formats, bitlength, getConstant)
      val assignment =
        if (mx == mr) Plus(ll, rr)
        else if (mx <= mr) RightShift(Plus(ll, rr), (mr - mx))
        else LeftShift(Plus(ll, rr), (mx - mr))  // Fixme: really?
      Equals(vr, assignment)

    case EqualsF(vr, MinusF(lhs, rhs)) =>
      val resultFormat = formats(vr)
      val mx = resultFormat.f
      val (ll, rr, mr) = alignOperators(lhs, rhs, formats, bitlength, getConstant)
      val assignment =
        if (mx == mr) Minus(ll, rr)
        else if (mx <= mr) RightShift(Minus(ll, rr), (mr - mx))
        else LeftShift(Minus(ll, rr), (mx - mr))  // Fixme: really?
      Equals(vr, assignment)

    case EqualsF(vr, TimesF(lhs, rhs)) =>
      val resultFormat = formats(vr)
      val mx = resultFormat.f
      val (mult, mr) = multiplyOperators(lhs, rhs, formats, bitlength, getConstant)
      val assignment =
        if (mx == mr) mult
        else if (mr - mx >= 0) RightShift(mult, (mr - mx))
        else LeftShift(mult, mx - mr)
      Equals(vr, assignment)

    case EqualsF(vr, DivisionF(lhs, rhs)) =>
      val resultFormat = formats(vr)
      val mx = resultFormat.f
      Equals(vr, divideOperators(lhs, rhs, mx, formats, bitlength, getConstant))

    case EqualsF(vr, rhs) => Equals(vr, translateToFP(rhs, formats, bitlength, getConstant))

    case v @ Variable(id) => v
    case FloatLiteral(r, exact) =>
      val bits = FPFormat.getFormat(r, bitlength).f
      getConstant(r, bits)
    case UMinusF( t ) => UMinus(translateToFP(t, formats, bitlength, getConstant))
  }


  private def alignOperators(x: Expr, y: Expr, formats: Map[Expr, FPFormat], bitlength: Int,
    getConstant: (Rational, Int) => Expr): (Expr, Expr, Int) = (x, y) match {
    case (v1 @ Variable(_), v2 @ Variable(_)) =>
      val my = formats(v1).f
      val mz = formats(v2).f

      if (mz == my) (v1, v2, my)
      else if (my <= mz) (LeftShift(v1, (mz - my)), v2, mz)
      else (v1, LeftShift(v2, (my - mz)), my)

    case (v @ Variable(_), FloatLiteral(r, exact)) =>
      val my = formats(v).f
      val mz = FPFormat.getFormat(r, bitlength).f

      val const = getConstant(r, mz)
      if (my == mz) (v, const, mz)
      else if (my <= mz) (LeftShift(v, (mz - my)), const, mz)
      else (v, LeftShift(const, (my - mz)), my)

    case (FloatLiteral(r, exact), v @ Variable(_)) =>
      val mz = formats(v).f
      val my = FPFormat.getFormat(r, bitlength).f
      val const = getConstant(r, my)
      if (my == mz) (const, v, mz)
      else if (my <= mz) (LeftShift(const, (mz - my)), v, mz)
      else (const, LeftShift(v, (my - mz)), my)

    case (FloatLiteral(r1, exact1), FloatLiteral(r2, exact2)) =>
      val my = FPFormat.getFormat(r1, bitlength).f
      val mz = FPFormat.getFormat(r2, bitlength).f
      val i1 = getConstant(r1, my)
      val i2 = getConstant(r2, mz)
      if (my == mz) (i1, i2, mz)
      else if (my <= mz) (LeftShift(i1, (mz - my)), i2, mz)
      else (i1, LeftShift(i2, (my - mz)), my)
  }

  def multiplyOperators(x: Expr, y: Expr, formats: Map[Expr, FixedPointFormat], bitlength: Int,
    getConstant: (Rational, Int) => Expr): (Times, Int) = (x, y) match {
    case (v1 @ Variable(_), v2 @ Variable(_)) =>
      val my = formats(v1).f
      val mz = formats(v2).f
      (Times(v1, v2), my + mz)

    case (v @ Variable(_), FloatLiteral(r, exact)) =>
      val my = formats(v).f
      val mz = FPFormat.getFormat(r, bitlength).f
      val i = getConstant(r, mz)
      (Times(v, i), my + mz)

    case (FloatLiteral(r, exact), v @ Variable(_)) =>
      val my = FPFormat.getFormat(r, bitlength).f
      val i = getConstant(r, my)
      val mz = formats(v).f
      (Times(i, v), my + mz)

    case (FloatLiteral(r1, exact1), FloatLiteral(r2, exact2)) =>
      val my = FPFormat.getFormat(r1, bitlength).f
      val i1 = getConstant(r1, my)
      val mz = FPFormat.getFormat(r2, bitlength).f
      val i2 = getConstant(r2, mz)
      (Times(i1, i2), my + mz)
   }

  def divideOperators(x: Expr, y: Expr, mx: Int, formats: Map[Expr, FixedPointFormat], bitlength: Int,
    getConstant: (Rational, Int) => Expr): Division = (x, y) match {
    case (v1 @ Variable(_), v2 @ Variable(_)) =>
      val my = formats(v1).f
      val mz = formats(v2).f
      val shift = mx + mz - my
      Division(LeftShift(v1, shift), v2)

    case (v @ Variable(_), FloatLiteral(r, exact)) =>
      val my = formats(v).f
      val mz = FPFormat.getFormat(r, bitlength).f
      val i = getConstant(r, mz)
      val shift = mx + mz - my
      Division(LeftShift(v, shift), i)

    case (FloatLiteral(r, exact), v @ Variable(_)) =>
      val my = FPFormat.getFormat(r, bitlength).f
      val i = getConstant(r, my)
      val mz = formats(v).f
      val shift = mx + mz - my
      Division(LeftShift(i, shift), v)

    case (FloatLiteral(r1, exact1), FloatLiteral(r2, exact2)) =>
      val my = FPFormat.getFormat(r1, bitlength).f
      val i1 = getConstant(r1, my)
      val mz = FPFormat.getFormat(r2, bitlength).f
      val i2 = getConstant(r2, mz)
      val shift = mx + mz - my
      Division(LeftShift(i1, shift), i2)
    }


    /*def rationalToLong(r: Rational, f: Int): Long = {
      (r * Rational(math.pow(2, f))).roundToInt.toLong
    }

    def rationalToInt(r: Rational, f: Int): Int = {
      (r * Rational(math.pow(2, f))).roundToInt
    }*/


  /*
  // Convenience for readability of printouts
  class DeltaRemover extends TransformerWithPC {
    type C = Seq[Expr]
    val initC = Nil

    def register(e: Expr, path: C) = path :+ e

    override def rec(e: Expr, path: C) = e match {
      case LessEquals(Variable(id1), Variable(id2)) if (id1.toString.contains("#delta_") && id2.toString == "#eps") =>
        True
      case LessEquals(UMinus(Variable(id1)), Variable(id2)) if (id1.toString == "#eps" && id2.toString.contains("#delta_")) =>
        True
      case _ =>
        super.rec(e, path)
    }
  }

  class BoundsConverter(eps2: Variable, offset: Variable) extends TransformerWithPC {
    type C = Seq[Expr]
    val initC = Nil

    def register(e: Expr, path: C) = path :+ e

    override def rec(e: Expr, path: C) = e match {
      case LessEquals(UMinus(eps), delta) if (eps.toString == "#eps") => LessThan(UMinus(eps2), delta)
      case LessEquals(delta, eps) if (eps.toString == "#eps") => LessThan(delta, eps2)
      case Equals(eps, machineEps) if (eps.toString == "#eps") => Equals(eps2, machineEps)

      case LessEquals(r @ RationalLiteral(v), x) => LessThan(Minus(r, offset), x)
      case GreaterEquals(x, r @ RationalLiteral(v)) => GreaterThan(x, Minus(r, offset))
      case LessEquals(x, y) => LessThan(x, Plus(y, offset))
      case GreaterEquals(x, y) => GreaterThan(Plus(x, offset), y)
      case _ =>
        super.rec(e, path)
    }
  }*/
}
