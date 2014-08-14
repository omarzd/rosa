package leon
package experiments
import java.io.{PrintWriter, File}
import ceres.common.{DoubleDouble, QuadDouble => QD}

object TriangleExperiment {
  var r = new scala.util.Random(4731)
  
  def triangle(a: Double, b: Double, c: Double): Double = {
    val s = (a + b + c)/2.0
    math.sqrt(s * (s - a) * (s - b) * (s - c))
  }

  def triangle(a: QD, b: QD, c: QD): QD = {
    val s = (a + b + c)/2.0
    QD.sqrt(s * (s - a) * (s - b) * (s - c))
  }


  def run = {
    val writer = new PrintWriter(new File("triangle.txt"))
    val writerInset = new PrintWriter(new File("triangleInset.txt"))
    var i = 0
    var j = 0
    var k = 0
    var m = 0
    var n = 0
    var o = 0
    while(i < 200) {
      var take = false
      var inset = false
      val a = 1.0 + 8.0 * r.nextDouble
      val b = 1.0 + 8.0 * r.nextDouble
      val c = 1.0 + 8.0 * r.nextDouble

      if (a + b > c  && a + c > b && b + c > a) {
        val aq = QD(a); val bq = QD(b); val cq = QD(c);
        val trig = triangle(a, b, c)

        if (trig < 0.1){ i += 1; take = true}
        else if (trig < 1.0 && j < 200){ j += 1; take = true}
        else if (trig < 2.0 && k < 200){ k += 1; take = true; inset = true}
        //else if (trig > 1.0 && trig < 2.0 && m < 200){ m += 1; take = true}
        //else if (trig < 4.0 && n < 100){ n += 1; take = true}
        //else if (trig < 5.0 && o < 100){ o += 1; take = true}


        if (take) {
          val trigQD = triangle(aq, bq, cq)
          val error = QD.abs(trigQD - trig)
          //val relError = error / trigQD
          writer.write(trigQD + " " + error + "\n")
          if (inset) {
            println(trigQD + " " + error)  
            writerInset.write(trigQD + " " + error + "\n")
          }
          
        }
      }
    }

    writer.close
    writerInset.close
  }

}
