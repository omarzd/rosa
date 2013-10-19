/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._

import xlang.Trees._
import real.Trees._
import real.RationalAffineUtils._
import VCKind._

object TreeOps {

  /* ----------------------
         Analysis phase
   ------------------------ */
  // can return several, as we may have an if-statement
  def getInvariantCondition(expr: Expr): List[Expr] = expr match {
    case IfExpr(cond, thenn, elze) => getInvariantCondition(thenn) ++ getInvariantCondition(elze)
    case Let(binder, value, body) => getInvariantCondition(body)
    case LessEquals(_, _) | LessThan(_, _) | GreaterThan(_, _) | GreaterEquals(_, _) => List(expr)
    case Equals(_, _) => List(expr)
    case _ =>
      println("!!! Expected invariant, but found: " + expr.getClass)
      List(BooleanLiteral(false))
  }

  // Has to run before we removed the lets!
  // Basically the first free expression that is not an if or a let is the result
  def addResult(expr: Expr): Expr = expr match {
    case ifThen @ IfExpr(_, _, _) => Equals(ResultVariable(), ifThen)
    case Let(binder, value, body) => Let(binder, value, addResult(body))
    case UMinusR(_) | PlusR(_, _) | MinusR(_, _) | TimesR(_, _) | DivisionR(_, _) | SqrtR(_) | FunctionInvocation(_, _) | Variable(_) =>
      Equals(ResultVariable(), expr)
    case Block(exprs, last) => Block(exprs, addResult(last))
    case _ => expr
  }

  def convertLetsToEquals(expr: Expr): Expr = expr match {
    case Equals(l, r) => Equals(l, convertLetsToEquals(r))
    case IfExpr(cond, thenn, elze) =>
      IfExpr(cond, convertLetsToEquals(thenn), convertLetsToEquals(elze))

    case Let(binder, value, body) =>
      And(Equals(Variable(binder), convertLetsToEquals(value)), convertLetsToEquals(body))

    case Block(exprs, last) =>
      And(exprs.map(e => convertLetsToEquals(e)) :+ convertLetsToEquals(last))

    case _ => expr
  }


  /* -----------------------
             Paths
   ------------------------- */
  def getPaths(expr: Expr): Set[Path] = {
    val partialPaths = collectPaths(expr)
    partialPaths.map(p => Path(p.condition, And(p.expression)))
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
  class AssertionCollector(outerFunDef: FunDef, precondition: Expr, variables: VariablePool) extends TransformerWithPC {
    type C = Seq[Expr]
    val initC = Nil

    val roundoffRemover = new RoundoffRemover

    var vcs = Seq[VerificationCondition]()

    def register(e: Expr, path: C) = path :+ e

    override def rec(e: Expr, path: C) = e match {
      case FunctionInvocation(funDef, args) if (funDef.precondition.isDefined) =>
        val pathToFncCall = And(path)
        val arguments: Map[Expr, Expr] = funDef.args.map(decl => decl.toVariable).zip(args).toMap
        val toProve = replace(arguments, roundoffRemover.transform(funDef.precondition.get))

        val allFncCalls = functionCallsOf(pathToFncCall).map(invc => invc.funDef.id.toString)
        vcs :+= new VerificationCondition(outerFunDef, Precondition, precondition, pathToFncCall, toProve, allFncCalls, variables)
        e               

      case Assertion(toProve) =>
        val pathToAssertion = And(path)
        val allFncCalls = functionCallsOf(pathToAssertion).map(invc => invc.funDef.id.toString)
        vcs :+= new VerificationCondition(outerFunDef, Assert, precondition, pathToAssertion, toProve, allFncCalls, variables)
        e
      case _ =>
        super.rec(e, path)
    }
  } 

  /*
    Replace the function call with its specification. For translation to Z3 FncValue needs to be translated
    with a fresh variable. For approximation, translate the spec into an XFloat.
  */
  class PostconditionInliner extends TransformerWithPC { //(reporter: Reporter, vcMap: Map[FunDef, VerificationCondition]) extends TransformerWithPC {
    type C = Seq[Expr]
    val initC = Nil

    //val postComplete = new CompleteSpecChecker

    def register(e: Expr, path: C) = path :+ e

    override def rec(e: Expr, path: C) = e match {
      case FunctionInvocation(funDef, args) =>
        val arguments: Map[Expr, Expr] = funDef.args.map(decl => decl.toVariable).zip(args).toMap
        
        // TODO
        /*val firstChoice = funDef.postcondition
        val secondChoice = vcMap(funDef).spec
        val post = firstChoice match {
          case Some(post) if (postComplete.check(post)) => Some(post)
          case _ => secondChoice match {
            case Some(post) if (postComplete.check(post)) => Some(post)
            case _ => None
          }
        }*/
        funDef.postcondition match {
          case Some(post) => FncValue(replace(arguments, post))
          case None =>
            throw PostconditionInliningFailedException("missing postcondition for " + funDef.id.name)
        }
        
      case _ =>
          super.rec(e, path)
    }
  }

  class FunctionInliner(fncs: Map[FunDef, Fnc]) extends TransformerWithPC { //(reporter: Reporter, vcMap: Map[FunDef, VerificationCondition]) extends TransformerWithPC {
    type C = Seq[Expr]
    val initC = Nil

    def register(e: Expr, path: C) = path :+ e

    override def rec(e: Expr, path: C) = e match {
      case FunctionInvocation(funDef, args) =>
        // TODO: I think we'll have a problem with same named variables
        val arguments: Map[Expr, Expr] = funDef.args.map(decl => decl.toVariable).zip(args).toMap
        val fncBody = fncs(funDef).body
        
        println("fnc body before: " + fncBody)
        val newBody = replace(arguments, fncBody)
        println("newBody: " + newBody)
        FncBody(funDef.id.name, newBody)
        
      case _ =>
          super.rec(e, path)
    }
  }

  // Overkill?
  /*class CompleteSpecChecker extends TransformerWithPC {
    type C = Seq[Expr]
    val initC = Nil

    var lwrBound = false
    var upBound = false
    var noise = false

    def register(e: Expr, path: C) = path :+ e

    override def rec(e: Expr, path: C) = e match {
      case LessEquals(RationalLiteral(lwrBnd), ResultVariable()) => lwrBound = true; e
      case LessThan(RationalLiteral(lwrBnd), ResultVariable()) => lwrBound = true; e
      case LessEquals(ResultVariable(), RationalLiteral(upBnd)) => upBound = true; e
      case LessThan(ResultVariable(), RationalLiteral(upBnd)) => upBound = true; e
      case Noise(ResultVariable(), _) => noise = true; e
      case _ =>
        super.rec(e, path)
    }

    def check(e: Expr): Boolean = {
      lwrBound = false; upBound = false; noise = false
      rec(e, initC)
      lwrBound && upBound && noise
    }
  }*/

  //@param (bounds, errors, extra specs)
  def getResultSpec(expr: Expr): (RationalInterval, Rational, Expr) = {
    val rc = new ResultCollector
    rc.transform(expr)
    (RationalInterval(rc.lwrBound.get, rc.upBound.get), rc.error.get, And(rc.extras))
  }

  // Assume that the spec is complete
  private class ResultCollector extends TransformerWithPC {
    type C = Seq[Expr]
    val initC = Nil
    var lwrBound: Option[Rational] = None
    var upBound: Option[Rational] = None
    var error: Option[Rational] = None
    var extras = List[Expr]()
    //var errorExpr: Option[Expr] = None

    def initCollector = {
      lwrBound = None; upBound = None; error = None; //errorExpr = None
    }

    def register(e: Expr, path: C) = path :+ e

    // FIXME: this should probably be done in register
    override def rec(e: Expr, path: C) = e match {
      case LessEquals(RealLiteral(lwrBnd), ResultVariable()) => lwrBound = Some(lwrBnd); e
      case LessEquals(ResultVariable(), RealLiteral(uprBnd)) => upBound = Some(uprBnd); e
      case LessEquals(IntLiteral(lwrBnd), ResultVariable()) => lwrBound = Some(Rational(lwrBnd)); e
      case LessEquals(ResultVariable(), IntLiteral(uprBnd)) => upBound = Some(Rational(uprBnd)); e
      case LessThan(RealLiteral(lwrBnd), ResultVariable()) => lwrBound = Some(lwrBnd); e
      case LessThan(ResultVariable(), RealLiteral(uprBnd)) =>  upBound = Some(uprBnd); e
      case LessThan(IntLiteral(lwrBnd), ResultVariable()) => lwrBound = Some(Rational(lwrBnd)); e
      case LessThan(ResultVariable(), IntLiteral(uprBnd)) => upBound = Some(Rational(uprBnd)); e
      case GreaterEquals(RealLiteral(uprBnd), ResultVariable()) =>  upBound = Some(uprBnd); e
      case GreaterEquals(ResultVariable(), RealLiteral(lwrBnd)) => lwrBound = Some(lwrBnd); e
      case GreaterEquals(IntLiteral(uprBnd), ResultVariable()) => upBound = Some(Rational(uprBnd)); e
      case GreaterEquals(ResultVariable(), IntLiteral(lwrBnd)) => lwrBound = Some(Rational(lwrBnd)); e
      case GreaterThan(RealLiteral(uprBnd), ResultVariable()) =>  upBound = Some(uprBnd); e
      case GreaterThan(ResultVariable(), RealLiteral(lwrBnd)) => lwrBound = Some(lwrBnd); e
      case GreaterThan(IntLiteral(uprBnd), ResultVariable()) => upBound = Some(Rational(uprBnd)); e
      case GreaterThan(ResultVariable(), IntLiteral(lwrBnd)) => lwrBound = Some(Rational(lwrBnd)); e

      case Noise(ResultVariable(), RealLiteral(value)) => error = Some(value); e
      case Noise(ResultVariable(), IntLiteral(value)) => error = Some(Rational(value)); e

      case Times(_, _) | Plus(_, _) | Division(_, _) | Minus(_, _) | UMinus(_) =>
        throw new Exception("found integer arithmetic in ResultCollector")
        null

      //case Noise(ResultVariable(), x) => errorExpr = Some(x); e
      case _ =>
        // TODO: extras
        super.rec(e, path)
    }
  }

  /* -----------------------
             Misc
   ------------------------- */
  class NoiseRemover extends TransformerWithPC {
    type C = Seq[Expr]
    val initC = Nil

    def register(e: Expr, path: C) = path :+ e

    override def rec(e: Expr, path: C) = e match {
      case Noise(_, _) => True
      case Roundoff(_) => True
      case _ =>
        super.rec(e, path)
    }
  }

  class RoundoffRemover extends TransformerWithPC {
    type C = Seq[Expr]
    val initC = Nil

    def register(e: Expr, path: C) = path :+ e

    override def rec(e: Expr, path: C) = e match {
      case Roundoff(_) => True
      case _ =>
        super.rec(e, path)
    }
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
      case ResultVariable() => FResVariable()
      case RealLiteral(r) => new FloatLiteral(r)
      case IfExpr(cond, thenn, elze) => FloatIfExpr(rec(cond, path), rec(thenn, path), rec(elze, path))
      case Equals(l, r) => EqualsF(rec(l, path), rec(r, path))
      // leave conditions on if-then-else in reals, as they will be passed as conditions to Z3
      case LessEquals(_,_) | LessThan(_,_) | GreaterEquals(_,_) | GreaterThan(_,_) => e

      case FncValue(s) => FncValueF(s)
      case FncBody(n, b) => FncBodyF(n, rec(b, path))
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
    And(And(LessEquals(RealLiteral(s.bounds.xlo), ResultVariable()),
            LessEquals(ResultVariable(), RealLiteral(s.bounds.xhi))),
            Noise(ResultVariable(), RealLiteral(s.absError)))
  }

  /* --------------------
        Arithmetic ops
   ---------------------- */
  val productCollector = new ProductCollector
  val powerTransformer = new PowerTransformer
  val factorizer = new Factorizer
  val minusDistributor = new MinusDistributor

  def massageArithmetic(expr: Expr): Expr = {
    //TODO: somehow remove redundant definitions of errors? stuff like And(Or(idealPart), Or(actualPart))
    val t1 = minusDistributor.transform(expr)
    //println("t1: " + t1.getClass)
    val t2 = factorizer.transform(factorizer.transform(t1))
    //println("t2: " + t2)
    val t3 = productCollector.transform(t2)
    //println("t3: " + t3)
    val t4 = powerTransformer.transform(t3)
    //println("t4: " + t4)
    simplifyArithmetic(t4)
  }


  def collectPowers(expr: Expr): Expr = {
    val t2 = productCollector.transform(expr)
    val t3 = powerTransformer.transform(t2)
    t3
  }

  class ProductCollector extends TransformerWithPC {
    type C = Seq[Expr]
    val initC = Nil
    
    def register(e: Expr, path: C) = path :+ e

    override def rec(e: Expr, path: C) = e match {
      case TimesR(l, r) =>
        val lhs = rec(l, path)
        val rhs = rec(r, path)
        Product(lhs, rhs)

      case _ =>
        super.rec(e, path)
    }
  }

  class PowerTransformer extends TransformerWithPC {
    type C = Seq[Expr]
    val initC = Nil
    
    def register(e: Expr, path: C) = path :+ e

    override def rec(e: Expr, path: C) = e match {
      case Product(exprs) =>
        val groups: Map[String, Seq[Expr]] = exprs.groupBy[String]( expr => expr.toString )
        val groupsRec = groups.map( x =>
          if (x._2.size == 1) {
            rec(x._2.head, path)
          } else {
            PowerR(rec(x._2.head, path), IntLiteral(x._2.size))
          }
        )
          
        groupsRec.tail.foldLeft[Expr](groupsRec.head)((x, y) => TimesR(x, y))
        
      case _ =>
        super.rec(e, path)
    }
  }

  class Factorizer extends TransformerWithPC {
    type C = Seq[Expr]
    val initC = Nil
    
    def register(e: Expr, path: C) = path :+ e

    override def rec(e: Expr, path: C) = e match {
      case TimesR(f, PlusR(a, b)) => PlusR(rec(TimesR(f, a), path), rec(TimesR(f, b), path))
      case TimesR(PlusR(a, b), f) => PlusR(rec(TimesR(a, f), path), rec(TimesR(b, f), path))
      case TimesR(f, MinusR(a, b)) => MinusR(rec(TimesR(f, a), path), rec(TimesR(f, b), path))
      case TimesR(MinusR(a, b), f) => MinusR(rec(TimesR(a, f), path), rec(TimesR(b, f), path))
      case Times(_, _) | Plus(_, _) | Division(_, _) | Minus(_, _) | UMinus(_) =>
        throw new Exception("found integer arithmetic in Factorizer")
        null
      case _ => super.rec(e, path)
    }
  }


  class MinusDistributor extends TransformerWithPC {
    type C = Seq[Expr]
    val initC = Nil
    
    def register(e: Expr, path: C) = path :+ e

    override def rec(e: Expr, path: C) = e match {
      case UMinusR(PlusR(x, y)) => MinusR(rec(UMinusR(x), path), rec(y, path))
      case UMinusR(MinusR(x, y)) => PlusR(rec(UMinusR(x), path), rec(y, path))
      case UMinusR(TimesR(x, y)) => TimesR(rec(UMinusR(x), path), rec(y, path))
      case UMinusR(DivisionR(x, y)) => DivisionR(rec(UMinusR(x), path), rec(y, path))
      case UMinusR(UMinusR(x)) => rec(x, path)
      case Times(_, _) | Plus(_, _) | Division(_, _) | Minus(_, _) | UMinus(_) =>
        throw new Exception("found integer arithmetic in MinusDistributor " + e)
        null
      case _ =>
        super.rec(e, path)
    }

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