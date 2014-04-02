/* Copyright 2009-2013 EPFL, Lausanne */

package leon.test
package real

import leon.purescala.Trees._
import leon.purescala.Common._
import leon.real.Trees._
import leon.real.TreeOps._
import leon.real.Rational

class RedundantTest extends LeonTestSuite {

  def vr(n: String): Variable = {
    Variable(FreshIdentifier(n)).setType(leon.purescala.TypeTrees.RealType)
  }

  def lit(i: Int): Expr = RealLiteral(Rational(i))

  val True = BooleanLiteral(true)
  val False = BooleanLiteral(false)

  test("trivial") {
    val body = vr("x")
    val post = vr("y")

    assert(removeRedundantConstraints(body, post) === Set.empty)
  }

  test("easy") {
    val res = vr("res")

    val body = And(LessThan(vr("x"), vr("y")), Equals(res, lit(99)))

    val post = LessThan(res, lit(100)) 

    assert(removeRedundantConstraints(body, post) === Set(Equals(res, lit(99))))
  }

  test("3 vars") {
    val res = vr("res")
    val a = vr("a")
    val b = vr("b")
    val x = vr("x")


    val body = Seq(LessThan(x, vr("y")), Equals(x, lit(76)))
    val needed = Set(LessThan(b, lit(34)), Equals(a, b), Equals(res, a))

    val post = LessThan(res, lit(100)) 

    assert(removeRedundantConstraints(And(body ++ needed.toSeq), post) === needed)
  }
}