package leon
package experiments

import ceres.common.{DoubleDouble, QuadDouble => QD}

object OpenLoopExperiments {

  def mean = {
    var r = new scala.util.Random(4731)

    class MeanDouble {
      var mean = 0.0
      var i = 1

      // returns the number selected
      def next: Double = {
        val xn = -50.00 + 400.0 * r.nextDouble
        mean = mean + (xn - mean) / i.toDouble
        i += 1
        xn
      }
    }

    class MeanQD {
      var mean = QD(0.0)
      var i = 1

      def next(xn: Double) = {
        mean = mean + (QD(xn) - mean) / QD(i.toDouble)
        i += 1
      }
    }

    val d = new MeanDouble
    val q = new MeanQD

    for (i <- 0 until 500) {
      val xn = d.next
      q.next(xn)

      printErrors(i, d.mean, q.mean)
    }
  }

  def variance1 = {
    var r = new scala.util.Random(4731)

    class VarianceDouble {
      var sumSimple = 0.0
      var sumSquared = 0.0
      var variance = 0.0

      var i = 1.0

      // returns the number selected
      def next(xn: Double) = {
        sumSimple = sumSimple + xn
        sumSquared = sumSquared + xn*xn

        variance = sumSquared/i - (sumSimple/i)*(sumSimple/i)
        i += 1.0
      }
    }

    class VarianceQD {
      var sumSimple = QD(0.0)
      var sumSquared = QD(0.0)
      var variance = QD(0.0)

      var i = QD(1.0)

      // returns the number selected
      def next(xn: Double) = {
        sumSimple = sumSimple + xn
        sumSquared = sumSquared + xn*xn

        variance = sumSquared/i - (sumSimple/i)*(sumSimple/i)
        i += QD(1.0)
      }
    }

    val d = new VarianceDouble
    val q = new VarianceQD

    for (i <- 0 until 500) {
      val xn = -50.00 + 400.0 * r.nextDouble
      d.next(xn)
      q.next(xn)

      printErrors(i, d.variance, q.variance)
    }
  }

  // computes the square of the variance
  def variance2 = {
    var r = new scala.util.Random(4731)

    class VarianceDouble {
      var mean = 0.0
      var variance = 0.0
      var i = 1.0

      // returns the number selected
      def next(xn: Double) = {
        val oldMean = mean
        mean = mean + (xn - mean) / i
        variance = (variance + (xn - oldMean)*(xn - mean))/i
        i += 1.0
      }
    }

    class VarianceQD {
      var mean = QD(0.0)
      var variance = QD(0.0)
      var i = QD(1.0)

      // returns the number selected
      def next(xn: Double) = {
        val oldMean = mean
        mean = mean + (xn - mean) / i
        variance = (variance + (xn - oldMean)*(xn - mean))/i
        i += QD(1.0)
      }
    }

    val d = new VarianceDouble
    val q = new VarianceQD

    for (i <- 0 until 500) {
      val xn = -50.00 + 400.0 * r.nextDouble
      d.next(xn)
      q.next(xn)

      printErrors(i, d.variance, q.variance)
    }
  }



  private def printErrors(i: Int, x: Double, xQ: QD) = {
    val errX = xQ - QD(x)
      
    print(i + ": ")
    print(x + ", " + errX)
    println(", rel: " + (errX / xQ))
  }

  private def printErrors(i: Int, x: Double, y: Double, xQ: QD, yQ: QD) = {
    val errX = xQ - QD(x)
    val errY = yQ - QD(y)
      
    print(i + ": ")
    print(x + ", " + y + ", ")
    print(errX + ", " + errY)
    println(", rel: " + (errX / xQ) + ", " + (errY / yQ))
  }
}