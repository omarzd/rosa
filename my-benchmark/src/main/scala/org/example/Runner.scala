package org.example

import com.google.caliper.{Runner => CaliperRunner}

object Runner {

  def main(args: Array[String]) {

    val benchmarks = if (args.size > 0) args else Array("sines", "floatVsDouble")

    benchmarks.foreach { _ match {
      case "sines" => CaliperRunner.main(classOf[Benchmark]) //args: _*)
      case "floatVsDouble" => CaliperRunner.main(classOf[FloatVsDoubleBenchmark])//args: _*)
      case "floatVsFixed" => CaliperRunner.main(classOf[FloatVsFixedBenchmark])
      case _ => println("unknown benchmark")
    }}
    
  }
  
}