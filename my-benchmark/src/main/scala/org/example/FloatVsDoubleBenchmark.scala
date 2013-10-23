package org.example

import annotation.tailrec
import com.google.caliper.Param

import scala.util.Random._

// a caliper benchmark is a class that extends com.google.caliper.Benchmark
// the SimpleScalaBenchmark trait does it and also adds some convenience functionality
class FloatVsDoubleBenchmark extends SimpleScalaBenchmark {
  
  // to make your benchmark depend on one or more parameterized values, create fields with the name you want
  // the parameter to be known by, and add this annotation (see @Param javadocs for more details)
  // caliper will inject the respective value at runtime and make sure to run all combinations 
  @Param(Array("10", "100", "1000", "10000"))
  val length: Int = 0
  
  var inputsFloat: Array[(Float, Float)] = _
  var inputsDouble: Array[(Double, Double)] = _
  
  override def setUp() {
    def getRandomFloat: Float = if (nextFloat < 0.5) - nextFloat * 100 else nextFloat * 100
    
    inputsFloat = Array.fill(length) { (getRandomFloat, getRandomFloat) }
    inputsDouble = inputsFloat.map(i => (i._1.toDouble, i._2.toDouble))

  }
  
  // the actual code you'd like to test needs to live in one or more methods
  // whose names begin with 'time' and which accept a single 'reps: Int' parameter
  // the body of the method simply executes the code we wish to measure, 'reps' times
  // you can use the 'repeat' method from the SimpleScalaBenchmark trait to repeat with relatively low overhead
  // however, if your code snippet is very fast you might want to implement the reps loop directly with 'while'
  def timeFloatJetEngine(reps: Int) = repeat(reps) {
    var result = 0.0f
    inputsFloat.foreach { x => 
      result += jetEngineFloat(x._1, x._2)
    }
    result // always have your snippet return a value that cannot easily be "optimized away"
  }

  private def jetEngineFloat(x1: Float, x2: Float): Float = {
    val t = (3*x1*x1 + 2*x2 - x1)
    x1 + ((2*x1*(t/(x1*x1 + 1))*
    (t/(x1*x1 + 1) - 3) + x1*x1*(4*(t/(x1*x1 + 1))-6))*
    (x1*x1 + 1) + 3*x1*x1*(t/(x1*x1 + 1)) + x1*x1*x1 + x1 +
    3*((3*x1*x1 + 2*x2 -x1)/(x1*x1 + 1)))
  }
  
  
  def timeDoubleJetEngine(reps: Int) = repeat(reps) {
    var result = 0.0
    inputsDouble.foreach { x => 
      result += jetEngineDouble(x._1, x._2)
    }
    result // always have your snippet return a value that cannot easily be "optimized away"
  }

  private def jetEngineDouble(x1: Double, x2: Double): Double = {
    val t = (3*x1*x1 + 2*x2 - x1)
    x1 + ((2*x1*(t/(x1*x1 + 1))*
    (t/(x1*x1 + 1) - 3) + x1*x1*(4*(t/(x1*x1 + 1))-6))*
    (x1*x1 + 1) + 3*x1*x1*(t/(x1*x1 + 1)) + x1*x1*x1 + x1 +
    3*((3*x1*x1 + 2*x2 -x1)/(x1*x1 + 1)))
  }
  
}

