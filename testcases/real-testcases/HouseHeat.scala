import leon.Real
import Real._

/*
  Example adapted from Matlab's 'Thermal Model of a House' example.
*/
object HouseHeat {

  // The air exiting the heater has a constant temperature which is a heater property. THeater = 50 deg C
  val t_heater = 50
  // TinIC = initial indoor temperature = 20 deg C
  val TinIC = 20


  var heater_on = false

  def heater(t_in: Real): Real = {

    // We may be able to express this with a requirement in the precondition
    if (t_in < 65) heater_on = true
    if (t_in > 75) heater_on = false

    if (heater_on) {
      // Air flow rate Mdot = 1 kg/sec = 3600 kg/hr
      val Mdot = 3600 // hour is the time unit
      // c = cp of air (273 K) = 1005.4 J/kg-K
      val c = 1005.4
      val dQ_dt = (t_heater - t_in) * Mdot * c
      dQ_dt // heat flow out of heater
    } else {
      0.0 // heater is off, no air flow
    }
  }

  def house(dq_dt: Real, t_out: Real, t_in: Real): Real = {
    val timestep = 0.1

    // c = cp of air (273 K) = 1005.4 J/kg-K
    val c = 1005.4
    val dq_loss = (t_in - t_out) / thermalResistance
    val dt_in = 1/(internalAirMass * c) * (dq_dt - dq_loss)
    t_in + timestep * dt_in
  }


  // Determine total internal air mass = M, Density of air at sea level = 1.2250 kg/m^3
  def internalAirMass(): Real = {
    // Pi in degrees
    val r2d = 180/math.Pi

    // Define the house geometry
    val lenHouse = 30 // house length
    val widHouse = 10 // house width
    val htHouse = 4 // house height
    val pitRoof = 40/r2d // roof pitch
    val densAir = 1.2250
    
    (lenHouse*widHouse*htHouse+math.tan(pitRoof)*widHouse*lenHouse)*densAir // M
  }

  // Determine the thermal resistance of the house
  def thermalResistance(): Real = {
    // Pi in degrees
    val r2d = 180/math.Pi

    // Define the house geometry
    val lenHouse = 30 // house length
    val widHouse = 10 // house width
    val htHouse = 4 // house height
    val pitRoof = 40/r2d // roof pitch
    val numWindows = 6 // number of windows
    val htWindows = 1 // height of windows
    val widWindows = 1 // width of windows
    val windowArea = numWindows*htWindows*widWindows
    val wallArea = 2*lenHouse*htHouse + 2*widHouse*htHouse + 2*(1/math.cos(pitRoof/2))*widHouse*lenHouse + math.tan(pitRoof)*widHouse - windowArea

    // Define the type of insulation used
    // Glass wool in the walls, 0.2 m thick, k is in units of J/sec/m/C - convert to J/hr/m/C multiplying by 3600
    val kWall = 0.038*3600   // hour is the time unit
    val LWall = .2
    val RWall = LWall/(kWall*wallArea)
  
    // Glass windows, 0.01 m thick  
    val kWindow = 0.78*3600  // hour is the time unit
    val LWindow = .01
    val RWindow = LWindow/(kWindow*windowArea)
  

    RWall*RWindow/(RWall + RWindow)  // Req

  }

  // Outdoor temperature, as a function of time
  def tempOutdoors(t: Real): Real = {
    val dailyTempVariationFrequency = 2 * math.Pi / 24 
    val dailyTempVariationPhase = 0.0
    val dailyTempVariationAmplitude = 15.0
    val dailyTempVariationBias = 0.0
    val avgOutdoorTempValue = 50
    (math.sin(dailyTempVariationFrequency * t + dailyTempVariationPhase) * dailyTempVariationAmplitude + dailyTempVariationBias) + avgOutdoorTempValue
  }

  

}