/* Copyright 2009-2013 EPFL, Lausanne */

package leon.test
package real

import leon.real.{RMatrix}
import leon.real.{Rational => R}
import R._

class MatrixOps extends LeonTestSuite {



  val m1 = RMatrix(Seq(Seq(1,2,3),
                       Seq(3,2,1),
                       Seq(2,1,3)))

  val m2 = RMatrix(Seq(Seq(4,5,6),
                       Seq(6,5,4),
                       Seq(4,6,5)))

  val i2 = RMatrix(Seq(Seq(1, 0), Seq(0, 1)))
  val i3 = RMatrix(Seq(Seq(1, 0, 0), Seq(0, 1, 0), Seq(0, 0, 1)))

  val t1 = Seq(R(4), R(5), R(6))
  val t2 = Seq(R(1), R(2), R(3))

  test("matrix mult 1") {
    val result = m1 * m2
    val trueResult = RMatrix(Seq(Seq(28,33,29),
                                 Seq(28,31,31),
                                 Seq(26,33,31)))

    assert(result === trueResult)
  }

  test("matrix mult 1 - wrong") {
    val result = m1 * m2
    val trueResult = RMatrix(Seq(Seq(29,33,29),
                                 Seq(28,31,31),
                                 Seq(26,33,31)))
    assert(result != trueResult)
  }


  test("matrix mult 2") {
    val result = m2 * m1
    val trueResult = RMatrix(Seq(Seq(31, 24, 35), Seq(29, 26, 35), Seq(32, 25, 33)))
    assert(result === trueResult)
  }

  test("inverse m1") {

    val inverse = m1.inverse

    val trueResult = RMatrix(3, Seq(Seq(R(-5,12), R(1,4), R(1,3)), 
                                    Seq(R(7,12), R(1,4), R(-2,3)),
                                    Seq(R(1,12), R(-1,4), R(1,3))))
    assert(inverse === trueResult)
  }

  test("inverse m2") {

    val inverse = (m1*m2).inverse

    val trueResult = RMatrix(3, Seq(Seq(R(31,180), R(11,60), R(-31,90)), 
                                    Seq(R(31,180), R(-19,60), R(7,45)),
                                    Seq(R(-59,180), R(11,60), R(7,45))))
    assert(inverse === trueResult)
  }

  test("identity") {
    assert(RMatrix.identity(2) === i2)
    assert(RMatrix.identity(3) === i3)
  }

  test("minus m2 - m1") {
    val result = m2 - m1

    val trueResult = RMatrix(Seq(Seq(3,3,3), Seq(3,3,3), Seq(2,5,2)))
    assert(result === trueResult)
  }

  test("power m1 5") {
    val result = m1.power(5)

    val trueResult = RMatrix(Seq(Seq(2512, 2060, 3204), Seq(2520, 2060, 3196), Seq(2516, 2056, 3204)))
    assert(result === trueResult)
  }


  test("power m2 6") {
    val result = m2.power(6)

    val trueResult = RMatrix(Seq(Seq(3577226, 4047909, 3765490), Seq(3577214, 4047911, 3765500),
      Seq(3577224, 4047904, 3765497)))
    assert(result === trueResult)
  }

  test("m1 * t1") {
    val result = m1*t1

    val trueResult = Seq(R(32), R(28), R(31))
    assert(result === trueResult)
  }

  test("m2 * t2") {
    val result = m2*t2

    val trueResult = Seq(R(32), R(28), R(31))
    assert(result === trueResult)
  }
}
