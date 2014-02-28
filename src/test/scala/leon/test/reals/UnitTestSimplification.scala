/* Copyright 2009-2013 EPFL, Lausanne */

package leon.test
package real

import leon.real.Prover._

import leon.purescala.Trees._
import leon.purescala.Common._
import leon.real.Trees._
import leon.real.{Rational => R}
import R._
import leon.purescala.TypeTrees._

class UnitTestSimplification extends LeonTestSuite {
  val x = Variable(FreshIdentifier("x")).setType(RealType)
  val y = Variable(FreshIdentifier("y")).setType(RealType)
  val z = Variable(FreshIdentifier("z")).setType(RealType)

  val el1 = And(LessEquals(RealLiteral(R(3.0)), x), LessEquals(RealLiteral(R(2.0)), x))
  val el2 = And(Seq(LessEquals(RealLiteral(R(2.0)), x), Equals(y, z), LessEquals(RealLiteral(R(3.0)), x)))

  val el3 = And(LessEquals(RealLiteral(R(3.0)), x), LessThan(RealLiteral(R(2.0)), x))
  val el4 = And(Seq(LessThan(RealLiteral(R(2.0)), x), Equals(y, z), LessThan(RealLiteral(R(3.0)), x)))


  val eu1 = And(GreaterEquals(RealLiteral(R(3.0)), x), GreaterEquals(RealLiteral(R(2.0)), x))
  val eu2 = And(Seq(GreaterEquals(RealLiteral(R(2.0)), x), Equals(y, z), GreaterEquals(RealLiteral(R(3.0)), x)))

  val ee1 = And(Seq(Noise(x, RealLiteral(R(1e-6))), Noise(y, RealLiteral(R(1e-8))), Noise(x, RealLiteral(R(1e-7)))))

  val f1 = And(Seq(
    Equals(x, PlusR(y, RealLiteral(R(3.0)))),
    Equals(z, MinusR(x, y))
    ))

  test("lower bound") {
    assert(simplifyConstraint(el1) === LessEquals(RealLiteral(R(3.0)), x))
    assert(simplifyConstraint(el2) === And(LessEquals(RealLiteral(R(3.0)), x), Equals(y, z)) )
    assert(simplifyConstraint(el3) === el3)
    assert(simplifyConstraint(el4) === And(LessThan(RealLiteral(R(3.0)), x), Equals(y, z)) )
  }

  test("upper bound") {
    assert(simplifyConstraint(eu1) === LessEquals(x, RealLiteral(R(2.0))))
  }

  test("absError") {
    assert(simplifyConstraint(ee1) === And(Noise(x, RealLiteral(R(1e-7))), Noise(y, RealLiteral(R(1e-8)))))
  }

  test("equality") {
    assert(simplifyConstraint(f1) ===
      And(Equals(x, PlusR(y, RealLiteral(R(3.0)))),
        Equals(z, MinusR(PlusR(y, RealLiteral(R(3.0))), y))))
  }
}
