import leon.real._
import RealOps._
import annotations._

object Thermostat {

  // This is a straight-line example, making no assumptions about
  // the state of the controller

  /*
    @param current current heating level
    @param in input signal, i.e. input temperature
    @return output signal between [0, 1] denoting how much
            the heater should be switched on
  */
  def control(currentState: Real, in: Real): Real = {
    require(currentState \in (0, 1) && in \in (15, 35))

    // this is the simples controller possible
    if (in < lower_threshold) {
      1.0
    } else if (in > upper_threshold) {
      0.0
    } else {
      currentState
    }
  } ensuring (res => res \in (0, 1)
    /*
      when heater is off, res = 0.0: x' = -x + 15  , i.e. x -> 15
      when heater is on, res = 1.0: x' = -x + 35   , i.e. x -> 35
    */
    //temperature after one step does not go outside given bounds
    val nextTemp = x - 0.1*x + 0.1 * (15 + res * 20)
    nextTemp \in (20, 25)
    )

  @model
  def getCurrentTemp: Real = { ???
  } ensuring (res => )


  // The funny thing is, this never ends, and so has no postcondition.
  // Maybe not ideal?
  def controlRec(currentState: Real): Real = {
    require( currentState \in (0, 1) )

    val in = getCurrentTemp()
    // this is the simples controller possible
    val nextState = if (in < lower_threshold) {
      1.0
    } else if (in > upper_threshold) {
      0.0
    } else {
      currentState
    }
    val nextTemp = x - 0.1*x + 0.1 * (15 + nextState * 20)
    assert(nextTemp \in (20, 25))

    controlRec(nextState)
  }

}