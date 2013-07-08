package leon
package numerics


import purescala.Trees._
import purescala.TypeTrees._
import purescala.TreeOps._
import purescala.Definitions._
import purescala.Common._
import Utils._
import affine.Rational


object ArithmeticOps {
  val productCollector = new ProductCollector
  val powerTransformer = new PowerTransformer
  val factorizer = new Factorizer
  val minusDistributor = new MinusDistributor

  def totalMakeover(expr: Expr): Expr = {
    //TODO: somehow remove redundant definitions of errors? stuff like And(Or(idealPart), Or(actualPart))
    //println("original: " + expr)
    val t1 = minusDistributor.transform(expr)
    //println("after minus: " + t1)
    val t2 = factorize(t1)
    //println("after fact: " + t2)
    
    val t3 = collectPowers(t2)
    //println("after power: " + t3)
    
    val t4 = simplifyArithmetic(t3)
    //println("after simp: " + t4)
    
    t4
  }

  def distributeMinus(expr: Expr): Expr = {
    minusDistributor.transform(expr)
  }

  def factorize(expr: Expr): Expr = {
    //TODO: factorization
    factorizer.transform(factorizer.transform(expr))
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
      case Times(l, r) =>
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
          
        groupsRec.tail.foldLeft[Expr](groupsRec.head)((x, y) => Times(x, y))
        
      case _ =>
        super.rec(e, path)
    }

    private def getPowerOrExpr(elem: Expr, count: Int): Expr = {
      if (count == 1) elem
      else Power(elem, IntLiteral(count))
    }   

    private def getPowerOrExpr(elems: Seq[Expr]): Expr = {
      if (elems.size == 1) elems.head
      else Power(elems.head, IntLiteral(elems.size))
    }
  }

  class Factorizer extends TransformerWithPC {
    type C = Seq[Expr]
    val initC = Nil
    
    def register(e: Expr, path: C) = path :+ e

    override def rec(e: Expr, path: C) = e match {
      case Times(f, Plus(a, b)) =>
        Plus(rec(Times(f, a), path), rec(Times(f, b), path))
      case Times(Plus(a, b), f) =>
        Plus(rec(Times(a, f), path), rec(Times(b, f), path))
      case Times(f, Minus(a, b)) =>
        Minus(rec(Times(f, a), path), rec(Times(f, b), path))
      case Times(Minus(a, b), f) =>
        Minus(rec(Times(a, f), path), rec(Times(b, f), path))
      case _ =>
        super.rec(e, path)
    }

  }


  class MinusDistributor extends TransformerWithPC {
    type C = Seq[Expr]
    val initC = Nil
    
    def register(e: Expr, path: C) = path :+ e

    override def rec(e: Expr, path: C) = e match {
      case UMinus(Plus(x, y)) => Minus(rec(UMinus(x), path), rec(y, path))
      case UMinus(Minus(x, y)) => Plus(rec(UMinus(x), path), rec(y, path))

      case UMinus(Times(x, y)) => Times(rec(UMinus(x), path), rec(y, path))

      case UMinus(Division(x, y)) => Division(rec(UMinus(x), path), rec(y, path))

      case UMinus(UMinus(x)) => rec(x, path)
      case _ =>
        super.rec(e, path)
    }

  }

   // Copied from TreeOps, added RationalLiteral
  def simplifyArithmetic(expr: Expr): Expr = {
    def simplify0(expr: Expr): Expr = expr match {
      case Plus(IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1 + i2)
      case Plus(IntLiteral(0), e) => e
      case Plus(e, IntLiteral(0)) => e
      case Plus(e1, UMinus(e2)) => Minus(e1, e2)
      case Plus(Plus(e, IntLiteral(i1)), IntLiteral(i2)) => Plus(e, IntLiteral(i1+i2))
      case Plus(Plus(IntLiteral(i1), e), IntLiteral(i2)) => Plus(IntLiteral(i1+i2), e)

      case Plus(RationalLiteral(i1), RationalLiteral(i2)) => RationalLiteral(i1 + i2)
      case Plus(RationalLiteral(z), e) if (z == Rational.zero) => e
      case Plus(e, RationalLiteral(z)) if (z == Rational.zero) => e
      case Plus(Plus(e, RationalLiteral(i1)), RationalLiteral(i2)) => Plus(e, RationalLiteral(i1+i2))
      case Plus(Plus(RationalLiteral(i1), e), RationalLiteral(i2)) => Plus(RationalLiteral(i1+i2), e)


      case Minus(e, IntLiteral(0)) => e
      case Minus(IntLiteral(0), e) => UMinus(e)
      case Minus(IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1 - i2)
      case UMinus(IntLiteral(x)) => IntLiteral(-x)
      case Minus(e, RationalLiteral(z)) if (z == Rational.zero) => e
      case Minus(RationalLiteral(z), e) if (z == Rational.zero) => UMinus(e)
      case Minus(RationalLiteral(i1), RationalLiteral(i2)) => RationalLiteral(i1 - i2)
      case UMinus(RationalLiteral(x)) => RationalLiteral(-x)

      case Minus(e1, UMinus(e2)) => Plus(e1, e2)
      case Minus(e1, Minus(UMinus(e2), e3)) => Plus(e1, Plus(e2, e3))
      case UMinus(UMinus(x)) => x
      case UMinus(Plus(UMinus(e1), e2)) => Plus(e1, UMinus(e2))
      case UMinus(Minus(e1, e2)) => Minus(e2, e1)

      
      case Times(IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1 * i2)
      case Times(IntLiteral(1), e) => e
      case Times(IntLiteral(-1), e) => UMinus(e)
      case Times(e, IntLiteral(1)) => e
      case Times(IntLiteral(0), _) => IntLiteral(0)
      case Times(_, IntLiteral(0)) => IntLiteral(0)
      case Times(IntLiteral(i1), Times(IntLiteral(i2), t)) => Times(IntLiteral(i1*i2), t)
      case Times(IntLiteral(i1), Times(t, IntLiteral(i2))) => Times(IntLiteral(i1*i2), t)
      case Times(IntLiteral(i), UMinus(e)) => Times(IntLiteral(-i), e)
      case Times(UMinus(e), IntLiteral(i)) => Times(e, IntLiteral(-i))
      case Times(IntLiteral(i1), Division(e, IntLiteral(i2))) if i2 != 0 && i1 % i2 == 0 => Times(IntLiteral(i1/i2), e)

      case Times(RationalLiteral(i1), RationalLiteral(i2)) => RationalLiteral(i1 * i2)
      case Times(RationalLiteral(o), e) if (o == Rational.one) => e
      case Times(RationalLiteral(no), e) if (no == -Rational.one) => UMinus(e)
      case Times(e, RationalLiteral(o)) if (o == Rational.one) => e
      case Times(RationalLiteral(z), _) if (z == Rational.zero) => RationalLiteral(Rational.zero)
      case Times(_, RationalLiteral(z)) if (z == Rational.zero) => RationalLiteral(Rational.zero)
      case Times(RationalLiteral(i1), Times(RationalLiteral(i2), t)) => Times(RationalLiteral(i1*i2), t)
      case Times(RationalLiteral(i1), Times(t, RationalLiteral(i2))) => Times(RationalLiteral(i1*i2), t)
      case Times(RationalLiteral(i), UMinus(e)) => Times(RationalLiteral(-i), e)
      case Times(UMinus(e), RationalLiteral(i)) => Times(e, RationalLiteral(-i))
      

      case Division(IntLiteral(i1), IntLiteral(i2)) if i2 != 0 => IntLiteral(i1 / i2)
      case Division(e, IntLiteral(1)) => e
      case Division(RationalLiteral(i1), RationalLiteral(i2)) if i2 != 0 => RationalLiteral(i1 / i2)
      case Division(e, RationalLiteral(o)) if (o == Rational.one) => e

      case Power(RationalLiteral(o), e) if (o == Rational.one) => RationalLiteral(Rational.one)

      //here we put more expensive rules
      //btw, I know those are not the most general rules, but they lead to good optimizations :)
      case Plus(UMinus(Plus(e1, e2)), e3) if e1 == e3 => UMinus(e2)
      case Plus(UMinus(Plus(e1, e2)), e3) if e2 == e3 => UMinus(e1)
      case Minus(e1, e2) if e1 == e2 => IntLiteral(0)
      case Minus(Plus(e1, e2), Plus(e3, e4)) if e1 == e4 && e2 == e3 => IntLiteral(0)
      case Minus(Plus(e1, e2), Plus(Plus(e3, e4), e5)) if e1 == e4 && e2 == e3 => UMinus(e5)

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