package leon
package numerics


import purescala.Trees._
import purescala.TypeTrees._
import purescala.TreeOps._
import purescala.Definitions._
import purescala.Common._
import Utils._


object ArithmeticOps {
  val productCollector = new ProductCollector
  val powerTransformer = new PowerTransformer
  val factorizer = new Factorizer

  def totalMakeover(expr: Expr): Expr = {
    collectPowers(factorize(expr))
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
        val t = Plus(rec(Times(f, a), path), rec(Times(f, b), path))
        //if(t != e) { println("\n e: " + e); println("t: " + t)}
        t
      case Times(Plus(a, b), f) =>
        val t = Plus(rec(Times(a, f), path), rec(Times(b, f), path))
        //if(t != e) { println("\n e: " + e); println("t: " + t)}
        t
      case Times(f, Minus(a, b)) =>
        val t = Minus(rec(Times(f, a), path), rec(Times(f, b), path))
        //if(t != e) { println("\n e: " + e); println("t: " + t)}
        t
      case Times(Minus(a, b), f) =>
        val t = Minus(rec(Times(a, f), path), rec(Times(b, f), path))
        //if(t != e) { println("\n e: " + e); println("t: " + t)}
        t
      case _ =>
        super.rec(e, path)
    }

  }

}