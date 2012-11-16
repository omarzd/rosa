package leon.synthesis

import leon.purescala.Trees._
import leon.purescala.TreeOps._
import leon.purescala.Common._

/*
 * TODO: move those functions to TreeOps
 */

object ArithmeticNormalization {

  case class NonLinearExpressionException(msg: String) extends Exception

  //assume the function is an arithmetic expression, not a relation
  //return a normal form where the [t a1 ... an] where
  //expr = t + a1*x1 + ... + an*xn and xs = [x1 ... xn]
  def apply(expr: Expr, xs: Array[Identifier]): Array[Expr] = {

    def containsId(e: Expr, id: Identifier): Boolean = e match {
      case Times(e1, e2) => containsId(e1, id) || containsId(e2, id)
      case IntLiteral(_) => false
      case Variable(id2) => id == id2
      case err => throw NonLinearExpressionException("unexpected in containsId: " + err)
    }

    def group(es: Seq[Expr], id: Identifier): Expr = {
      val totalCoef = es.foldLeft(0)((acc, e) => {
        val (IntLiteral(i), id2) = extractCoef(e)
        assert(id2 == id)
        acc + i
      })
      Times(IntLiteral(totalCoef), Variable(id))
    }

    var expandedForm: Seq[Expr] = expand(expr)
    val res: Array[Expr] = new Array(xs.size + 1)

    xs.zipWithIndex.foreach{case (id, index) => {
      val (terms, rests) = expandedForm.partition(containsId(_, id))
      expandedForm = rests
      val Times(coef, Variable(_)) = group(terms, id)
      res(index+1) = coef
    }}

    res(0) = simplify(expandedForm.foldLeft[Expr](IntLiteral(0))(Plus(_, _)))
    res
  }


  //assume the expr is a literal (mult of constants and variables) with degree one
  def extractCoef(e: Expr): (Expr, Identifier) = {
    var id: Option[Identifier] = None
    var coef = 1

    def rec(e: Expr): Unit = e match {
      case IntLiteral(i) => coef = coef*i
      case Variable(id2) => if(id.isEmpty) id = Some(id2) else throw NonLinearExpressionException("multiple variable")
      case Times(e1, e2) => rec(e1); rec(e2)
    }

    rec(e)
    assert(!id.isEmpty)
    (IntLiteral(coef), id.get)
  }

  //multiply two sums together and distribute in a bigger sum
  def multiply(es1: Seq[Expr], es2: Seq[Expr]): Seq[Expr] = {
    es1.flatMap(e1 => es2.map(e2 => Times(e1, e2)))
  }


  def expand(expr: Expr): Seq[Expr] = expr match {
    case Plus(es1, es2) => expand(es1) ++ expand(es2)
    case Minus(e1, e2) => expand(e1) ++ expand(e2).map(Times(IntLiteral(-1), _): Expr)
    case UMinus(e) => expand(e).map(Times(IntLiteral(-1), _): Expr)
    case Times(es1, es2) => multiply(expand(es1), expand(es2))
    case v@Variable(_) => Seq(v)
    case n@IntLiteral(_) => Seq(n)
    case err => throw NonLinearExpressionException("unexpected in expand: " + err)
  }

  //simple, local simplifications
  //you should not assume anything smarter than some constant folding and simple cancelation
  //to avoid infinite cycle we only apply simplification that reduce the size of the tree
  def simplify(expr: Expr): Expr = {
    def simplify0(expr: Expr): Expr = expr match {
      case Plus(IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1 + i2)
      case Plus(IntLiteral(0), e) => e
      case Plus(e, IntLiteral(0)) => e
      case Plus(e1, UMinus(e2)) => Minus(e1, e2)

      case Minus(e, IntLiteral(0)) => e
      case Minus(IntLiteral(0), e) => UMinus(e)
      case Minus(IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1 - i2)
      case Minus(e1, UMinus(e2)) => Plus(e1, e2)
      case Minus(e1, Minus(UMinus(e2), e3)) => Plus(e1, Plus(e2, e3))

      case UMinus(IntLiteral(x)) => IntLiteral(-x)
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

      case Division(IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1 / i2)
      case Division(e, IntLiteral(1)) => e

      //here we put more expensive rules
      case Minus(e1, e2) if e1 == e2 => IntLiteral(0) 
      case e => e
    }
    def fix[A](f: (A) => A)(a: A): A = {
      val na = f(a)
      if(a == na) a else fix(f)(na)
    }
    val res = fix(simplePostTransform(simplify0))(expr)
    res
  }

  // Assume the formula consist only of top level AND, find a top level
  // Equals and extract it, return the remaining formula as well
  def extractEquals(expr: Expr): (Option[Equals], Expr) = expr match {
    case And(es) =>
      // OK now I'm just messing with you.
      val (r, nes) = es.foldLeft[(Option[Equals],Seq[Expr])]((None, Seq())) {
        case ((None, nes), eq @ Equals(_,_)) => (Some(eq), nes)
        case ((o, nes), e) => (o, e +: nes)
      }
      (r, And(nes.reverse))

    case e => (None, e)
  }
}