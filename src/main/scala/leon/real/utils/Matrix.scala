/* Copyright 2013-2014 EPFL, Lausanne */

package leon
package real

import ceres.common.DirectedRounding.{multUp}

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
  val rows: Seq[Seq[T]]
  def apply(i: Int, j: Int) = rows(i)(j)

  override def toString: String = {
    "\n" + rows.map(d => d.mkString(" | ")).mkString("\n")
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

  def fromDoubles(ints: Seq[Seq[Double]]): RMatrix = {
    RMatrix(ints(0).length, ints.map(row => row.map(e => Rational(e))))
  }

  def power(m: RMatrix, n: Int): RMatrix = {
    assert(n >= 0)
    if (n == 0) RMatrix.identity(m.dim)
    else if (n == 1) m
    else if (n % 2 == 0) power(m*m, n / 2)
    else m * power(m*m, (n-1)/2)
  }

  def powerWithDoubles(m: RMatrix, num: Int): RMatrix = {
    assert(num >= 0)

    def powerBySquare(m: DMatrix, n: Int): DMatrix = {
      if (n == 0) DMatrix.identity(m.dim)
      else if (n == 1) m
      else if (n % 2 == 0) powerBySquare(m*m, n / 2)
      else m * powerBySquare(m*m, (n-1)/2)
    }

    powerBySquare(m.toDouble, num).toRationals
  }

  def printArray(a: Array[Array[Rational]]) = {
    "\n" + a.map(r => r.mkString(", ")).mkString("\n")
  }

  def inverseGauss(m: RMatrix): RMatrix = {

    // create augmented matrix
    val am: Array[Array[Rational]] = m.rows.zipWithIndex.map({
      case (row, index) =>
        val identityRow: Array[Rational] = Array.fill(m.dim)(zero)
        identityRow(index) = one
        
        row.toArray ++ identityRow 
        
      }).toArray
    println("augmentedMatrix: " + printArray(am))


    // bring it into row echelon form

    for (j <- 0 until m.dim) {
      //println("\n\nj: " + j)
      // find maximum jth column element
      var tmp = j
      for (i <- j + 1 until m.dim) 
        if (abs(am(i)(j)) > abs(am(tmp)(j))) tmp = i

      //println("tmp: " + tmp)
      if (tmp != j) {
        val currentRow = am(j)
        val maxRow = am(tmp)
        am(j) = maxRow
        am(tmp) = currentRow
      }

      //println("am after swap: " + printArray(am))
    
      for (i <- 0 until m.dim) {

        if ( i != j) {
          // add or subtract a multiple of one row to another
          val r = am(i)(j)   // this is the multiple

          for (k <- 0 until (2 * m.dim)) {

            am(i)(k) = am(i)(k) - am(j)(k) * r / am(j)(j)
          }



        } else {
          // divide the current row by 
          val r = am(i)(j)
          //println("dividing by " + r)
          //println("before: " + am(i).mkString(", "))
          am(i) = am(i).map(elem => elem / r)
          //println("after: " + am(i).mkString(", "))
        }

      }// end row ops


    }// end outer for


    //println("final: " + printArray(am))

    // extract the inverse
    val res = am.map(row => row.drop(m.dim).toSeq).toSeq
    println("res: " + res)
    RMatrix(m.dim, res)
  }


}

object DMatrix {
  def identity(dim: Int): DMatrix = {
    val dta = Array.fill(dim, dim)(0.0)
    for(i <- 0 until dim) {
      dta(i)(i) = 1.0
    }
    DMatrix(dim, dta.map(r => r.toSeq).toSeq)
  }
}

case class DMatrix (val dim: Int, val rows: Seq[Seq[Double]]) extends Matrix[Double] {

  def *(y: DMatrix): DMatrix = {
    DMatrix(dim, rows.map({ arow =>
      y.columns.map({ bcoln =>
         arow.zip(bcoln).foldLeft(0.0)({
          case (sum, (a, b)) => sum + multUp(a, b)
          })
        })
    }))
  }

  private def columns: Seq[Seq[Double]] = {
    val firstRow = rows(0)

    firstRow.zipWithIndex.map({
      case (row, i) =>
        rows.map(r => r(i))
    })

  }

  def toRationals: RMatrix = {
    RMatrix(dim, rows.map({ arow =>
      arow.map( entry => Rational(entry))
    }))
  }

}

case class RMatrix (val dim: Int, val rows: Seq[Seq[Rational]]) extends Matrix[Rational] {
  //assert(data.length == dim)
  assert(rows.forall(d => d.length == dim))

  def isIdentity: Boolean = rows.forall(row => row.forall(elem => elem == one))

  def toDouble: DMatrix = {
    DMatrix(dim, rows.map({ arow =>
      arow.map( entry => entry.toDouble)
    }))
  }

  private def columns: Seq[Seq[Rational]] = {
    val firstRow = rows(0)

    firstRow.zipWithIndex.map({
      case (row, i) =>
        rows.map(r => r(i))
    })

  }

  def -(y:RMatrix): RMatrix = {
    RMatrix(dim, rows.zip(y.rows).map({
      case (arow, brow) =>
        arow.zip(brow).map({
          case (a, b) => a - b
          })
      }))
  }

  def *(y: RMatrix): RMatrix = {
    RMatrix(dim, rows.map({ arow =>
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

  def *(vec: Seq[Rational]): Seq[Rational] = {
    rows.map( row => {
      row.zip(vec).foldLeft(zero)({
        case (sum, (r, v)) => sum + r*v
        })
      })
  }

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

    case x if (x > 3) =>
      RMatrix.inverseGauss(this)
  }

  
}

class EMatrix private(dim: Int, val rows: Seq[Seq[Expr]]) extends Matrix[Expr] {
  //assert(data.length == dim)
  assert(rows.forall(d => d.length == dim))

  def map(f: Expr => Rational): RMatrix = {
    RMatrix(dim, rows.map(row => {
      row.map(elem => f(elem))
      }))
  }
}