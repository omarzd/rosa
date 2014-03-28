/* Copyright 2013-2014 EPFL, Lausanne */

package leon
package real

import purescala.Trees.{Expr}
import Rational._

object EMatrix {
  // sequence of rows
  def fromSeqs(es: Seq[Seq[Expr]]): EMatrix = {
    new EMatrix(es(0).length, es)
  }

}

// square matrix
trait Matrix[T] {
  val data: Seq[Seq[T]]
  def apply(i: Int, j: Int) = data(i)(j)

  override def toString: String = {
    "\n" + data.map(d => d.mkString(" | ")).mkString("\n")
  }


}

object RMatrix {

  def identity(dim: Int): RMatrix = {
    val dta = Array.fill(dim, dim)(zero)
    for(i <- 0 until dim) {
      dta(i)(i) = one
    }
    RMatrix(dim, dta.map(r => r.toSeq).toSeq)
  }

  def apply(ints: Seq[Seq[Int]]): RMatrix = {
    RMatrix(ints(0).length, ints.map(row => row.map(e => Rational(e))))
  }
}

case class RMatrix (dim: Int, val data: Seq[Seq[Rational]]) extends Matrix[Rational] {
  //assert(data.length == dim)
  assert(data.forall(d => d.length == dim))

  // TODO: redundant
  def rows: Seq[Seq[Rational]] = data

  def columns: Seq[Seq[Rational]] = {
    val firstRow = data(0)

    firstRow.zipWithIndex.map({
      case (row, i) =>
        rows.map(r => r(i))
    })

  }

  def -(y:RMatrix): RMatrix = {
    RMatrix(dim, data.zip(y.data).map({
      case (arow, brow) =>
        arow.zip(brow).map({
          case (a, b) => a - b
          })
      }))
  }

  def *(y: RMatrix): RMatrix = {
    RMatrix(dim, data.map({ arow =>
      y.columns.map({ bcoln =>
         arow.zip(bcoln).foldLeft(zero)({
          case (sum, (a, b)) => sum + a * b
          })
        })
    }))
  }

  def power(n: Int): RMatrix = {
    var x = this
    for (i <- 1 until n) {
      x = x * this
    }
    x
  }

  def *(vec: Seq[Rational])

  def determinant: Rational = dim match {
    case 2 =>
      val a = this(0,0); val b = this(0,1)
      val c = this(1,0); val d = this(1,1)
      this(0,0)*this(1,1) - this(0,1)*this(1,0)

    case 3 =>
      val a = this(0,0); val b = this(0,1); val c = this(0,2);
      val d = this(1,0); val e = this(1,1); val f = this(1,2);
      val g = this(2,0); val h = this(2,1); val i = this(2,2);

      a*(e*i - f*h) - b*(i*d - f*g) + c*(d*h - e*g)
  }

  def inverse: RMatrix = dim match {
    case 2 =>
      val a = this(0,0); val b = this(0,1)
      val c = this(1,0); val d = this(1,1)
      val det = determinant

      val newData = Seq(Seq(d / det, -b / det), Seq(-c / det, a / det))

      RMatrix(dim, newData)

    case 3 =>
      val a = this(0,0); val b = this(0,1); val c = this(0,2);
      val d = this(1,0); val e = this(1,1); val f = this(1,2);
      val g = this(2,0); val h = this(2,1); val i = this(2,2);
      val det = determinant

      val A = (e*i - f*h)/det
      val B = -(d*i - f*g)/det
      val C = (d*h - e*g)/det
      val D = -(b*i - c*h)/det
      val E = (a*i - c*g)/det
      val F = -(a*h - b*g)/det
      val G = (b*f - c*e)/det
      val H = -(a*f - c*d)/det
      val I = (a*e - b*d)/det

      val newData = Seq(Seq(A,D,G),
                        Seq(B,E,H),
                        Seq(C,F,I))
      RMatrix(dim, newData)
  }

  
}

class EMatrix private(dim: Int, val data: Seq[Seq[Expr]]) extends Matrix[Expr] {
  //assert(data.length == dim)
  assert(data.forall(d => d.length == dim))

  def map(f: Expr => Rational): RMatrix = {
    RMatrix(dim, data.map(row => {
      row.map(elem => f(elem))
      }))
  }
}