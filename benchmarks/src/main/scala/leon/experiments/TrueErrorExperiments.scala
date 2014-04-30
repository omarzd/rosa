package leon
package experiments

import ceres.common.{DoubleDouble, QuadDouble => QD}

object TrueErrorExperiments {

  def main(args: Array[String]) {

    val benchmarks = if (args.size > 0) args else Array("")

    benchmarks.foreach { _ match {
      case "sine" => SineExperiments.sine
      case "cube" => IterativeExperiments.cubeRoot(10.0, 5.4)
      case "newton" =>
        for(x <- List(0.18, 0.35, -0.53, 0.78, -0.99, 1.19, 1.25, -1.35, 1.89)) {
          IterativeExperiments.newtonSine(x)
        }
      case "harmonic" => SimulationExperiments.harmonicEuler
      case "harmonicRK" => SimulationExperiments.harmonicRK2
      case "harmonic4" => SimulationExperiments.harmonicRK4
      //case "verhulst" => verhulst(0.5f, 45.0f, 11.0f)
      //case "lotka" => lotkaVolterra
      case "nbody" => SimulationExperiments.nbody
      case "predatorPrey" => SimulationExperiments.predatorPrey(20.0, 20.0)
      case "predatorRK2" => SimulationExperiments.predatorPreyRK2(20.0, 20.0)
      case "predatorRK4" => SimulationExperiments.predatorPreyRK4(20.0, 20.0)
      case "mean" => OpenLoopExperiments.mean
      case "variance" => OpenLoopExperiments.variance1
      case "variance2" => OpenLoopExperiments.variance2
      case _ => println("unknown benchmark")
    }}
    
  }
}