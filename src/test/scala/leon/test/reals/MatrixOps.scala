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

  val m3 = RMatrix(Seq(Seq(8, 10, 9),
                       Seq(11, 12, 13),
                       Seq(7, 6, 2)))

  val m4 = RMatrix(Seq(Seq(12, 10, 11, 13),
                       Seq(2, 6, 14, 9),
                       Seq(5, 3, 4, 8),
                       Seq(7, 15, 16, 17)))

  val m5 = RMatrix(Seq(Seq(4, 11, 13, 7, 8),
                       Seq(3, 5, 9, 14, 6),
                       Seq(12, 10, 15 ,16, 17),
                       Seq(2, 18, 19, 20, 21),
                       Seq(22, 23, 24, 25, 26)))


  val m6 = RMatrix.fromDoubles(Seq(Seq(1.0125958110204192, 0., 0.022617800112495742, 0.1, 0. , 0.0005958662735577874),
                   Seq(0.005921762731020502, 1., 0.007539266704165247, 0., 0., 0.04413821270376106),
                   Seq(0.017765288193061505, 0., 1.0219721471017966, 0., 0.1, 0.0007944883647437166),
                   Seq(0.12595811020419093, 0., 0.22617800112495742, 1., 0., 0.005958662735577875),
                   Seq(0.17765288193061504, 0., 0.2197214710179657, 0., 1., 0.007944883647437166),
                   Seq(0.0005921762731020501, 0.1, 0.0007539266704165247, 0., 0., 0.9993808299347923)))

  val i2 = RMatrix(Seq(Seq(1, 0), Seq(0, 1)))
  val i3 = RMatrix(Seq(Seq(1, 0, 0), Seq(0, 1, 0), Seq(0, 0, 1)))

  val t1 = Seq(R(4), R(5), R(6))
  val t2 = Seq(R(1), R(2), R(3))

  /*test("matrix mult 1") {
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
  }*/

  test("inverse") {
    //val (RMatrix.identity(6) - m6).inverse
    val result = RMatrix.inverseGauss(RMatrix.identity(6) - m6)
    print("result: " + result)
    assert(true)
  }
}
