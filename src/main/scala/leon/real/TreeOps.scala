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

object TreeOps {

  def inIntervals(expr: Expr, vars: VariablePool): RationalInterval = expr match {
    case RationalLiteral(r) => RationalInterval(r, r)
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

  class NoiseRemover extends TransformerWithPC {
    type C = Seq[Expr]
    val initC = Nil

    def register(e: Expr, path: C) = path :+ e

    override def rec(e: Expr, path: C) = e match {
      case Noise(_, _) => True
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

      // leave conditions on if-then-else in reals
      case LessEquals(_,_) | LessThan(_,_) | GreaterEquals(_,_) | GreaterThan(_,_) => e

      case _ =>
        super.rec(e, path)
    }
  }

  val productCollector = new ProductCollector
  val powerTransformer = new PowerTransformer
  val factorizer = new Factorizer
  val minusDistributor = new MinusDistributor

  def massageArithmetic(expr: Expr): Expr = {
    //TODO: somehow remove redundant definitions of errors? stuff like And(Or(idealPart), Or(actualPart))
    val t1 = minusDistributor.transform(expr)
    val t2 = factorizer.transform(factorizer.transform(t1))
    val t3 = productCollector.transform(t2)
    val t4 = powerTransformer.transform(t3)
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
        val groupsRec = groups.map( x => getPowerOrExpr(rec(x._2.head, path), x._2.size))
          
        groupsRec.tail.foldLeft[Expr](groupsRec.head)((x, y) => TimesR(x, y))
        
      case _ =>
        super.rec(e, path)
    }

    private def getPowerOrExpr(elem: Expr, count: Int): Expr = {
      if (count == 1) elem
      else PowerR(elem, IntLiteral(count))
    }   

    private def getPowerOrExpr(elems: Seq[Expr]): Expr = {
      if (elems.size == 1) elems.head
      else PowerR(elems.head, IntLiteral(elems.size))
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
      case _ =>
        super.rec(e, path)
    }

  }

   // Copied from purescala.TreeOps, added RationalLiteral
   // TODO Not sure we need the IntLiterals here at all!
  def simplifyArithmetic(expr: Expr): Expr = {
    def simplify0(expr: Expr): Expr = expr match {
      case PlusR(IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1 + i2)
      case PlusR(IntLiteral(0), e) => e
      case PlusR(e, IntLiteral(0)) => e
      case PlusR(e1, UMinusR(e2)) => MinusR(e1, e2)
      case PlusR(PlusR(e, IntLiteral(i1)), IntLiteral(i2)) => PlusR(e, IntLiteral(i1+i2))
      case PlusR(PlusR(IntLiteral(i1), e), IntLiteral(i2)) => PlusR(IntLiteral(i1+i2), e)

      case PlusR(RationalLiteral(i1), RationalLiteral(i2)) => RationalLiteral(i1 + i2)
      case PlusR(RationalLiteral(z), e) if (z == Rational.zero) => e
      case PlusR(e, RationalLiteral(z)) if (z == Rational.zero) => e
      case PlusR(PlusR(e, RationalLiteral(i1)), RationalLiteral(i2)) => PlusR(e, RationalLiteral(i1+i2))
      case PlusR(PlusR(RationalLiteral(i1), e), RationalLiteral(i2)) => PlusR(RationalLiteral(i1+i2), e)


      case MinusR(e, IntLiteral(0)) => e
      case MinusR(IntLiteral(0), e) => UMinusR(e)
      case MinusR(IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1 - i2)
      case UMinusR(IntLiteral(x)) => IntLiteral(-x)
      case MinusR(e, RationalLiteral(z)) if (z == Rational.zero) => e
      case MinusR(RationalLiteral(z), e) if (z == Rational.zero) => UMinusR(e)
      case MinusR(RationalLiteral(i1), RationalLiteral(i2)) => RationalLiteral(i1 - i2)
      case UMinusR(RationalLiteral(x)) => RationalLiteral(-x)

      case MinusR(e1, UMinusR(e2)) => PlusR(e1, e2)
      case MinusR(e1, MinusR(UMinusR(e2), e3)) => PlusR(e1, PlusR(e2, e3))
      case UMinusR(UMinusR(x)) => x
      case UMinusR(PlusR(UMinusR(e1), e2)) => PlusR(e1, UMinusR(e2))
      case UMinusR(MinusR(e1, e2)) => MinusR(e2, e1)

      
      case TimesR(IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1 * i2)
      case TimesR(IntLiteral(1), e) => e
      case TimesR(IntLiteral(-1), e) => UMinusR(e)
      case TimesR(e, IntLiteral(1)) => e
      case TimesR(IntLiteral(0), _) => IntLiteral(0)
      case TimesR(_, IntLiteral(0)) => IntLiteral(0)
      case TimesR(IntLiteral(i1), TimesR(IntLiteral(i2), t)) => TimesR(IntLiteral(i1*i2), t)
      case TimesR(IntLiteral(i1), TimesR(t, IntLiteral(i2))) => TimesR(IntLiteral(i1*i2), t)
      case TimesR(IntLiteral(i), UMinusR(e)) => TimesR(IntLiteral(-i), e)
      case TimesR(UMinusR(e), IntLiteral(i)) => TimesR(e, IntLiteral(-i))
      case TimesR(IntLiteral(i1), DivisionR(e, IntLiteral(i2))) if i2 != 0 && i1 % i2 == 0 => TimesR(IntLiteral(i1/i2), e)

      case TimesR(RationalLiteral(i1), RationalLiteral(i2)) => RationalLiteral(i1 * i2)
      case TimesR(RationalLiteral(o), e) if (o == Rational.one) => e
      case TimesR(RationalLiteral(no), e) if (no == -Rational.one) => UMinusR(e)
      case TimesR(e, RationalLiteral(o)) if (o == Rational.one) => e
      case TimesR(RationalLiteral(z), _) if (z == Rational.zero) => RationalLiteral(Rational.zero)
      case TimesR(_, RationalLiteral(z)) if (z == Rational.zero) => RationalLiteral(Rational.zero)
      case TimesR(RationalLiteral(i1), TimesR(RationalLiteral(i2), t)) => TimesR(RationalLiteral(i1*i2), t)
      case TimesR(RationalLiteral(i1), TimesR(t, RationalLiteral(i2))) => TimesR(RationalLiteral(i1*i2), t)
      case TimesR(RationalLiteral(i), UMinusR(e)) => TimesR(RationalLiteral(-i), e)
      case TimesR(UMinusR(e), RationalLiteral(i)) => TimesR(e, RationalLiteral(-i))
      

      case DivisionR(IntLiteral(i1), IntLiteral(i2)) if i2 != 0 => IntLiteral(i1 / i2)
      case DivisionR(e, IntLiteral(1)) => e
      case DivisionR(RationalLiteral(i1), RationalLiteral(i2)) if i2 != 0 => RationalLiteral(i1 / i2)
      case DivisionR(e, RationalLiteral(o)) if (o == Rational.one) => e

      case PowerR(RationalLiteral(o), e) if (o == Rational.one) => RationalLiteral(Rational.one)

      //here we put more expensive rules
      //btw, I know those are not the most general rules, but they lead to good optimizations :)
      case PlusR(UMinusR(PlusR(e1, e2)), e3) if e1 == e3 => UMinusR(e2)
      case PlusR(UMinusR(PlusR(e1, e2)), e3) if e2 == e3 => UMinusR(e1)
      case MinusR(e1, e2) if e1 == e2 => IntLiteral(0)
      case MinusR(PlusR(e1, e2), PlusR(e3, e4)) if e1 == e4 && e2 == e3 => IntLiteral(0)
      case MinusR(PlusR(e1, e2), PlusR(PlusR(e3, e4), e5)) if e1 == e4 && e2 == e3 => UMinusR(e5)

      //default
      case e => e
    }
    def fix[A](f: (A) => A)(a: A): A = {
      val na = f(a)
      if(a == na) a else fix(f)(na)
    }


    val res = fix(simplePostTransform(simplify0))(expr)
    res
  }

}