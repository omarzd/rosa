/* Copyright 2009-2015 EPFL, Lausanne */

package leon.test
package real

import leon.real.RationalForm
import leon.real.Rational
import leon.real.Rational._

class AffineTest extends LeonTestSuite {

  test("radius") {
    val r = new RationalForm(one) :+ two :+ Rational(3.0) 

    println(r.longString)

    assert(r.radius === Rational(5.0))
  }

  test("plus exclusive") {
    val r = new RationalForm(one) :+ two :+ Rational(3.0) 
    val s = new RationalForm(zero) :+ one :+ two
    println(r.longString)
    println(s.longString)

    val t = r + s
    println(t.longString)
    assert(t.radius === Rational(8.0))
    assert(t.noise.length === 4)    
    assert(t.x0 === one)
  }

  test("plus exclusive associative") {
    val r = new RationalForm(one) :+ two :+ Rational(3.0) 
    val s = new RationalForm(zero) :+ one :+ two
    println(r.longString)
    println(s.longString)

    val t = s + r
    println(t.longString)
    assert(t.radius === Rational(8.0))
    assert(t.noise.length === 4)    
    assert(t.x0 === one)
  }

  test("plus incl") {
    val r = new RationalForm(one) :+ two :+ Rational(3.0) 
    val s = r :+ Rational(3.0)
    println(r.longString)
    println(s.longString)

    val t = r + s
    println(t.longString)
    assert(t.radius === Rational(13.0))
    assert(t.noise.length === 3)
    assert(t.x0 === two)
  }
  
  test("plus empty") {
    val r = new RationalForm(one) :+ two :+ Rational(3.0) 
    val s = new RationalForm(zero)
    println(r.longString)
    println(s.longString)

    val t = r + s
    println(t.longString)
    assert(t.radius === Rational(5.0))
    assert(t.noise.length === 2)
    assert(t.x0 === one) 
  }

  test("plus empty 2") {
    val r = new RationalForm(one)
    val s = new RationalForm(zero)
    println(r.longString)
    println(s.longString)

    val t = r + s
    println(t.longString)
    assert(t.radius === zero)
    assert(t.noise.length === 0)    
    assert(t.x0 === one)
  }

  test("unary") {
    val r = new RationalForm(one) :+ two :+ Rational(3.0) 
    println(r.longString)

    val t = - r
    println(t.longString)

    assert(t.radius === Rational(5.0))
    assert(t.noise.length === 2)
    assert(t.x0 === Rational(-1.0))
  }


  test("minus exclusive") {
    val r = new RationalForm(zero) :+ two :+ Rational(3.0) 
    val s = new RationalForm(one) :+ one :+ two
    println(r.longString)
    println(s.longString)

    val t = r - s
    println(t.longString)
    assert(t.radius === Rational(8.0))
    assert(t.noise.length === 4)    
    assert(t.x0 === Rational(-1.0))
  }

  test("minus equal") {
    val r = new RationalForm(one) :+ two :+ Rational(3.0) 
    println(r.longString)

    val t = r - r
    println(t.longString)
    assert(t.radius === zero)
    assert(t.noise.length === 0)    
    assert(t.x0 === zero)
  }

  test("mult zero") {
    val r = new RationalForm(one) :+ two :+ Rational(3.0) 
    val s = new RationalForm(zero)
    println(r.longString)
    println(s.longString)

    val t = r * s
    println(t.longString)
    assert(t.radius === zero)
    assert(t.noise.length === 0)
    assert(t.x0 === zero) 
  }

  test("mult exclusive") {
    val r = new RationalForm(one) :+ two :+ Rational(3.0) 
    val s = new RationalForm(two) :+ one :+ two
    println(r.longString)
    println(s.longString)

    val t = r * s
    println(t.longString)
    assert(t.radius === Rational(28))
    assert(t.noise.length === 5)    
    assert(t.x0 === two)
  }



}