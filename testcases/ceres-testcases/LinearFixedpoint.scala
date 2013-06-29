
import leon.Real
import Real._

object LinearFixedpoint {

  def ballBeam(state1: Real, state2: Real, state3: Real, state4: Real): Real = {
    require(state1.in(0.0, 1.0) && state2.in(-0.5, 0.5) && state3.in(0, 0.5)
      && state4.in(0, 0.5))
    (-1828.6) * state1 + (-1028.6) * state2 + (-2008.0) * state3 + (-104.0) * state4
  } ensuring (res => noise(res, 1e-7))

  def batchReactorOut1(state1: Real, state2: Real, state3: Real, state4: Real): Real = {
    require(state1.in(-1.0, 1.0) && state2.in(-1.0, 1.0) && state3.in(-1.0, 1.0)
      && state4.in(-1.0, 1.0))
   (-0.058300) * state1 + (-0.908300) * state2 + (-0.325800) * state3 + (-0.872100) * state4
  } ensuring (res => noise(res, 1e-7))

  def batchReactorOut2(state1: Real, state2: Real, state3: Real, state4: Real): Real = {
    require(state1.in(-1.0, 1.0) && state2.in(-1.0, 1.0) && state3.in(-1.0, 1.0)
      && state4.in(-1.0, 1.0))
   (2.463800) * state1 + (0.050400) * state2 + (1.709900) * state3 + (-1.165300) * state4
  } ensuring (res => noise(res, 1e-7))

  def batchReactorState1(state1: Real, state2: Real, state3: Real, state4: Real, y1: Real, y2: Real): Real = {
    require(state1.in(-1.0, 1.0) && state2.in(-1.0, 1.0) && state3.in(-1.0, 1.0) &&
      state4.in(-1.0, 1.0) && y1.in(-1.0, 1.0) && y2.in(-1.0, 1.0))

    (0.934292) * state1 + (0.008415) * state2 + (-0.014106) * state3 + (0.023954) * state4 + (0.077400) * y1 + (-0.010300) * y2
  } ensuring (res => noise(res, 1e-7))

  def batchReactorState2(state1: Real, state2: Real, state3: Real, state4: Real, y1: Real, y2: Real): Real = {
    require(state1.in(-1.0, 1.0) && state2.in(-1.0, 1.0) && state3.in(-1.0, 1.0) &&
      state4.in(-1.0, 1.0) && y1.in(-1.0, 1.0) && y2.in(-1.0, 1.0))

    (-0.006769) * state1 + (0.884924) * state2 + (-0.016066) * state3 + (-0.044019) * state4 + (-0.002200) * y1 + (0.022700) * y2
  } ensuring (res => noise(res, 1e-7))

  def batchReactorState3(state1: Real, state2: Real, state3: Real, state4: Real, y1: Real, y2: Real): Real = {
    require(state1.in(-1.0, 1.0) && state2.in(-1.0, 1.0) && state3.in(-1.0, 1.0) &&
      state4.in(-1.0, 1.0) && y1.in(-1.0, 1.0) && y2.in(-1.0, 1.0))

    (-0.092148) * state1 + (-0.011039) * state2 + (0.853511) * state3 + (0.107537) * state4 + (0.026700) * y1 + (0.039800) * y2
  } ensuring (res => noise(res, 1e-7))

  def batchReactorState4(state1: Real, state2: Real, state3: Real, state4: Real, y1: Real, y2: Real): Real = {
    require(state1.in(-1.0, 1.0) && state2.in(-1.0, 1.0) && state3.in(-1.0, 1.0) &&
      state4.in(-1.0, 1.0) && y1.in(-1.0, 1.0) && y2.in(-1.0, 1.0))

    (-0.036410) * state1 + (0.030194) * state2 + (-0.027155) * state3 + (1.004619) * state4 + (0.035600) * y1 + (0.000100) * y2
  } ensuring (res => noise(res, 1e-7))



  def trancair4Out(state0: Real, state1: Real, state2: Real, state3: Real, state4: Real,
    state5: Real, state6: Real, state7: Real, state8: Real): Real = {
    require(state0.in(-2.5, 6.5) && state1.in(-2.5, 6.5) && state2.in(-2.5, 6.5) &&
      state3.in(-2.5, 6.5) && state4.in(-2.0, 12.0) && state4.in(-2.0, 12.0) &&
      state5.in(-2.0, 12.0) && state6.in(-2.0, 12.0) && state7.in(-2.0, 12.0) && state8.in(-2.0, 12.0))

    (-1201.0) * state0  + (-4876.0) * state1  + 1.3415999999999998E+04 * state2  +
    (-10484.0) * state3  + (-774.0) * state4  + (-1.3620000000000002E+04) * state5  +
    10481.0 * state6  + 20425.0 * state7  + (-17815.0) * state8  + 5.2121094496644555E+03
  } ensuring (res => noise(res, 1e-7))

  def trancair4State1(state0: Real, state1: Real, state2: Real, state3: Real, state4: Real,
    state5: Real, state6: Real, state7: Real, state8: Real, y0: Real, y1: Real, y2: Real, y3: Real, y4: Real): Real = {
    require(state0.in(-2.5, 6.5) && state1.in(-2.5, 6.5) && state2.in(-2.5, 6.5) &&
      state3.in(-2.5, 6.5) && state4.in(-2.0, 12.0) && state4.in(-2.0, 12.0) &&
      state5.in(-2.0, 12.0) && state6.in(-2.0, 12.0) && state7.in(-2.0, 12.0) &&
      state8.in(-2.0, 12.0) && y0.in(-2, 12.0) && y1.in(-2, 12.0) && y2.in(-2, 12.0) &&
      y3.in(-2, 12.0) && y4.in(-2, 12.0))

      state0 + (-9.6239E-08)*state1+ (2.65102E-07)*state2+ (-2.07133E-07)*state3+ (6.97639E-05)*state4+ (-4.78152E-05)*state5+
       (-2.63725E-05)*state6+ (-1.05202E-05)*state7+ (-1.57626E-05)*state8 + (3.0220751E-05)*y0 + (-5.2453841E-05)*y1+
        (2.6579541E-05)*y2+ (1.0923688E-05)*y3+ (1.5410654E-05)*y4+ (1.9755163E-11)*5.2121094496644555E+03
  } ensuring (res => noise(res, 1e-7))

  def trancair4State2(state0: Real, state1: Real, state2: Real, state3: Real, state4: Real,
    state5: Real, state6: Real, state7: Real, state8: Real, y0: Real, y1: Real, y2: Real, y3: Real, y4: Real): Real = {
    require(state0.in(-2.5, 6.5) && state1.in(-2.5, 6.5) && state2.in(-2.5, 6.5) &&
      state3.in(-2.5, 6.5) && state4.in(-2.0, 12.0) && state4.in(-2.0, 12.0) &&
      state5.in(-2.0, 12.0) && state6.in(-2.0, 12.0) && state7.in(-2.0, 12.0) &&
      state8.in(-2.0, 12.0) && y0.in(-2, 12.0) && y1.in(-2, 12.0) && y2.in(-2, 12.0) &&
      y3.in(-2, 12.0) && y4.in(-2, 12.0))

    (-1.13598E-08)*state0 + (1.0)*state1+(1.2786E-07)*state2+(-9.96874E-08)*state3+
    (3.36288E-05)*state4+(3.94595E-05)*state5+(-6.09589E-05)*state6+(-3.51073E-05)*state7+
    (2.7313E-06)*state8+(-3.3636111E-05)*y0 + (6.0410747E-05)*y1+(-3.8941208E-05)*y2+ (3.5301806E-05)*y3+
    (-2.9009623E-06)*y4+ (9.522692E-12)*5.2121094496644555E+03
  } ensuring (res => noise(res, 1e-7))



  def trancair4State3(state0: Real, state1: Real, state2: Real, state3: Real, state4: Real,
    state5: Real, state6: Real, state7: Real, state8: Real, y0: Real, y1: Real, y2: Real, y3: Real, y4: Real): Real = {
    require(state0.in(-2.5, 6.5) && state1.in(-2.5, 6.5) && state2.in(-2.5, 6.5) &&
      state3.in(-2.5, 6.5) && state4.in(-2.0, 12.0) && state4.in(-2.0, 12.0) &&
      state5.in(-2.0, 12.0) && state6.in(-2.0, 12.0) && state7.in(-2.0, 12.0) &&
      state8.in(-2.0, 12.0) && y0.in(-2, 12.0) && y1.in(-2, 12.0) && y2.in(-2, 12.0) &&
      y3.in(-2, 12.0) && y4.in(-2, 12.0))
    (-3.85494E-09)*state0 +(-1.55578E-08)*state1+(1.0)*state2+(-3.33852E-08)*state3+ (1.13515E-05)*state4+
    (8.09597E-06)*state5+ (3.75166E-05)*state6+(-7.28888E-05)*state7+ (7.51347E-06)*state8 +
    (-1.1353997E-05)*y0 + (-8.1397399E-06)*y1+ (6.2517037E-05)*y2+
    (-2.7045432E-05)*y3+ (-7.570773E-06)*y4+ (3.2144001E-12)*5.2121094496644555E+03
  } ensuring (res => noise(res, 1e-7))


  def trancair4State4(state0: Real, state1: Real, state2: Real, state3: Real, state4: Real,
    state5: Real, state6: Real, state7: Real, state8: Real, y0: Real, y1: Real, y2: Real, y3: Real, y4: Real): Real = {
    require(state0.in(-2.5, 6.5) && state1.in(-2.5, 6.5) && state2.in(-2.5, 6.5) &&
      state3.in(-2.5, 6.5) && state4.in(-2.0, 12.0) && state4.in(-2.0, 12.0) &&
      state5.in(-2.0, 12.0) && state6.in(-2.0, 12.0) && state7.in(-2.0, 12.0) &&
      state8.in(-2.0, 12.0) && y0.in(-2, 12.0) && y1.in(-2, 12.0) && y2.in(-2, 12.0) &&
      y3.in(-2, 12.0) && y4.in(-2, 12.0))

    (-4.88831E-09)*state0 +(-1.94328E-08)*state1+(5.40591E-08)*state2+(1.0)*state3+ (1.41246E-05)*state4+
    (-1.33425E-05)*state5+ (4.35487E-06)*state6+(1.06102E-04)*state7+ (-9.66574E-05)*state8+
    (-1.4127737E-05)*y0 + (1.328804E-05)*y1+ (-4.3128989E-06)*y2+
    (-6.0208156E-06)*y3+ (-3.4137075E-06)*y4+ (3.9997189E-12)*5.2121094496644555E+03
  } ensuring (res => noise(res, 1e-7))


  def trancair4State5(state0: Real, state1: Real, state2: Real, state3: Real, state4: Real,
    state5: Real, state6: Real, state7: Real, state8: Real, y0: Real, y1: Real, y2: Real, y3: Real, y4: Real): Real = {
    require(state0.in(-2.5, 6.5) && state1.in(-2.5, 6.5) && state2.in(-2.5, 6.5) &&
      state3.in(-2.5, 6.5) && state4.in(-2.0, 12.0) && state4.in(-2.0, 12.0) &&
      state5.in(-2.0, 12.0) && state6.in(-2.0, 12.0) && state7.in(-2.0, 12.0) &&
      state8.in(-2.0, 12.0) && y0.in(-2, 12.0) && y1.in(-2, 12.0) && y2.in(-2, 12.0) &&
      y3.in(-2, 12.0) && y4.in(-2, 12.0))

    (-6.84591E-04)*state0 +(-0.00276041)*state1+(0.00759572)*state2+(-0.00593566)*state3+
    (0.999506)*state4+(-0.00770228)*state5+(0.00593952)*state6+ (0.0115632)*state7+ 
    (-0.0100812)*state8+(5.4816343E-05)*y0 + (-8.1959323E-06)*y1+
    (-5.0852166E-06)*y2+ (-1.5117184E-07)*y3+
    (-4.5614134E-06)*y4+ (5.6615597E-07)*5.2121094496644555E+03
  } ensuring (res => noise(res, 1e-7))


  def trancair4State6(state0: Real, state1: Real, state2: Real, state3: Real, state4: Real,
    state5: Real, state6: Real, state7: Real, state8: Real, y0: Real, y1: Real, y2: Real, y3: Real, y4: Real): Real = {
    require(state0.in(-2.5, 6.5) && state1.in(-2.5, 6.5) && state2.in(-2.5, 6.5) &&
      state3.in(-2.5, 6.5) && state4.in(-2.0, 12.0) && state4.in(-2.0, 12.0) &&
      state5.in(-2.0, 12.0) && state6.in(-2.0, 12.0) && state7.in(-2.0, 12.0) &&
      state8.in(-2.0, 12.0) && y0.in(-2, 12.0) && y1.in(-2, 12.0) && y2.in(-2, 12.0) &&
      y3.in(-2, 12.0) && y4.in(-2, 12.0))
    (7.81569E-06)*state0 +(-7.83331E-06)*state1+ (3.894E-08)*state2+ (-3.04854E-08)*state3+
    (1.02522E-05)*state4+ (0.999937)*state5+ (9.27415E-06)*state6+ (6.88119E-06)*state7+
    (-5.63471E-06)*state8 + (-9.161729E-06)*y0 + (6.1088274E-05)*y1+ (-8.1509892E-06)*y2+
    (-6.8219061E-06)*y3+ (5.5829936E-06)*y4+ (2.9031464E-12)*5.2121094496644555E+03
  } ensuring (res => noise(res, 1e-7))


  def trancair4State7(state0: Real, state1: Real, state2: Real, state3: Real, state4: Real,
    state5: Real, state6: Real, state7: Real, state8: Real, y0: Real, y1: Real, y2: Real, y3: Real, y4: Real): Real = {
    require(state0.in(-2.5, 6.5) && state1.in(-2.5, 6.5) && state2.in(-2.5, 6.5) &&
      state3.in(-2.5, 6.5) && state4.in(-2.0, 12.0) && state4.in(-2.0, 12.0) &&
      state5.in(-2.0, 12.0) && state6.in(-2.0, 12.0) && state7.in(-2.0, 12.0) &&
      state8.in(-2.0, 12.0) && y0.in(-2, 12.0) && y1.in(-2, 12.0) && y2.in(-2, 12.0) &&
      y3.in(-2, 12.0) && y4.in(-2, 12.0))
(-2.3463E-09)*state0 +(7.80955E-06)*state1+ (-7.79273E-06)*state2+ (-2.06835E-08)*state3+
 (6.95227E-06)*state4+ (8.71732E-06)*state5+ (0.999932)*state6+ (1.01306E-05)*state7+ (-1.09525E-06)*state8 +
  (-6.953786E-06)*y0 + (-7.6514151E-06)*y1+ (6.5402276E-05)*y2+ (-8.997669E-06)*y3+ (1.0601845E-06)*y4+ (1.9686912E-12)*5.2121094496644555E+03
  } ensuring (res => noise(res, 1e-7))


  def trancair4State8(state0: Real, state1: Real, state2: Real, state3: Real, state4: Real,
    state5: Real, state6: Real, state7: Real, state8: Real, y0: Real, y1: Real, y2: Real, y3: Real, y4: Real): Real = {
    require(state0.in(-2.5, 6.5) && state1.in(-2.5, 6.5) && state2.in(-2.5, 6.5) &&
      state3.in(-2.5, 6.5) && state4.in(-2.0, 12.0) && state4.in(-2.0, 12.0) &&
      state5.in(-2.0, 12.0) && state6.in(-2.0, 12.0) && state7.in(-2.0, 12.0) &&
      state8.in(-2.0, 12.0) && y0.in(-2, 12.0) && y1.in(-2, 12.0) && y2.in(-2, 12.0) &&
      y3.in(-2, 12.0) && y4.in(-2, 12.0))
(2.5093E-10)*state0 +(9.15884E-10)*state1+ (7.81656E-06)*state2+ (-7.81701E-06)*state3+
 (-6.54335E-07)*state4+ (6.87341E-06)*state5+ (1.00368E-05)*state6+ (0.999907)*state7+ (3.32876E-05)*state8 +
  (6.5448232E-07)*y0 + (-6.8708837E-06)*y1+ (-8.9460042E-06)*y2+ (9.0317123E-05)*y3+ (-3.2191562E-05)*y4+ (-1.8530512E-13)*5.2121094496644555E+03
  } ensuring (res => noise(res, 1e-7))

  def trancair4State9(state0: Real, state1: Real, state2: Real, state3: Real, state4: Real,
    state5: Real, state6: Real, state7: Real, state8: Real, y0: Real, y1: Real, y2: Real, y3: Real, y4: Real): Real = {
    require(state0.in(-2.5, 6.5) && state1.in(-2.5, 6.5) && state2.in(-2.5, 6.5) &&
      state3.in(-2.5, 6.5) && state4.in(-2.0, 12.0) && state4.in(-2.0, 12.0) &&
      state5.in(-2.0, 12.0) && state6.in(-2.0, 12.0) && state7.in(-2.0, 12.0) &&
      state8.in(-2.0, 12.0) && y0.in(-2, 12.0) && y1.in(-2, 12.0) && y2.in(-2, 12.0) &&
      y3.in(-2, 12.0) && y4.in(-2, 12.0))
(-1.73572E-09)*state0 +(-6.90441E-09)*state1+ (1.91831E-08)*state2+ (7.80416E-06)*state3+
 (5.01527E-06)*state4+ (-4.73947E-06)*state5+ (4.30545E-07)*state6+ (3.35281E-05)*state7+ (0.999934)*state8 +
  (-5.0163739E-06)*y0 + (4.7201386E-06)*y1+ (-4.156438E-07)*y2+ (-3.2406398E-05)*y3+ (6.4987306E-05)*y4+ (1.4201936E-12)*5.2121094496644555E+03
  } ensuring (res => noise(res, 1e-7))



}
