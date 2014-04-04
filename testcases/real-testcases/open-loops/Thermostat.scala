import leon.real._
import RealOps._
import annotations._

object Thermostat {

  // This is a straight-line example, making no assumptions about
  // the state of the controller

  /*
    Target temperature is 22 degrees.

    @param current current heating level
    @param in input signal, i.e. input temperature
    @return output signal between [0, 1] denoting how much
            the heater should be switched on
  */
  def control(currentState: Real, in: Real): Real = {
    require(0.0 <= currentState && currentState <= 1.0 && 
            15.0 <= in && in <= 35.0)

    // this is the simples controller possible
    if (in < 20.0) {
      1.0
    } else if (in > 25) {
      0.0
    } else {
      currentState
    }
  } ensuring (res => 0.0 <= res && res <= 1.0 &&
      15 <= x - 0.1*x + 0.1 * (15 + res * 20) &&
      x - 0.1*x + 0.1 * (15 + res * 20) <= 35
    /*
      when heater is off, res = 0.0: x' = -x + 15  , i.e. x -> 15
      when heater is on, res = 1.0: x' = -x + 35   , i.e. x -> 35

      temperature after one step does not go outside given bounds
      val nextTemp = x - 0.1*x + 0.1 * (15 + res * 20)
      nextTemp \in (20, 25)
    */
    )

  // We could also model the fact that the temperature can only change by so much,
  // by passing in the last known temp. and maybe the timespan
  /*@model or external or input
  def getCurrentTemp: Real = {
    ???
  } ensuring (res =>
    15.0 <= res && res <= 35.0
   )


  // The funny thing is, this never ends, and so has no postcondition.
  // Maybe not ideal?
  def controlRec(currentState: Real): Real = {
    require( 0.0 <= currentState && currentState <= 1.0 )

    val in = getCurrentTemp()

    // this is the simples controller possible
    val nextState = if (in < 20.0) {
      1.0
    } else if (in > 25.0) {
      0.0
    } else {
      currentState
    }
    val projectedTemp = x - 0.1*x + 0.1 * (15 + nextState * 20)
    assert( 15.0 <= nextTemp && nextTemp <= 25.0 )

    controlRec(nextState)
  } ensuring ( true )
  */
}