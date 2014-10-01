package leon
package benchmark

import com.google.caliper.{Runner => CaliperRunner}

object Runner {

  def main(args: Array[String]) {

    val benchmarks = if (args.size > 0) args else Array("sines", "floatVsDouble")

    benchmarks.foreach { _ match {
      case "sines" => CaliperRunner.main(classOf[Benchmark]) //args: _*)
      case "floatVsDouble" => CaliperRunner.main(classOf[FloatVsDoubleBenchmark])//args: _*)
      case "floatVsFixed" => CaliperRunner.main(classOf[FloatVsFixedBenchmark])
      case "doppler" => CaliperRunner.main(classOf[DopplerBenchmark])
      case "jetEngine" => CaliperRunner.main(classOf[JetEngineBenchmark])
      case "turbine" => CaliperRunner.main(classOf[TurbineBenchmark])
      case "sine" => CaliperRunner.main(classOf[SineBenchmark])
      
      case _ => println("unknown benchmark")
    }}
    
  }
  
}