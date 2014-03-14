/* Copyright 2009-2014 EPFL, Lausanne */
import leon.real._
import RealOps._

object PhysicsApproxUnknown {

  def turbine1Star(v: Real, w: Real, r: Real): Real = {
    require(-4.5 <= v && v <= -0.3 && 0.4 <= w && w <= 0.9 && 3.8 <= r && r <= 7.8 &&
      v +/- 1e-7 && w +/- 1e-12 && r +/- 1e-8)

    3 + 2/(r*r) - 0.125*(3-2*v)*(w*w*r*r)/(1-v) - 4.5
  } ensuring(res => -18.525727 < res && res < -1.991604 && res +/- 4.855806e-6)

  def turbine1(v: Real, w: Real, r: Real): Real = {
    require(-4.5 <= v && v <= -0.3 && 0.4 <= w && w <= 0.9 && 3.8 <= r && r <= 7.8)

    3 + 2/(r*r) - 0.125*(3-2*v)*(w*w*r*r)/(1-v) - 4.5
  } ensuring(res => -18.525727 < res && res < -1.991604 && res +/- 1.24161e-13)

  def turbine2Star(v: Real, w: Real, r: Real): Real = {
    require(-4.5 <= v && v <= -0.3 && 0.4 <= w && w <= 0.9 && 3.8 <= r && r <= 7.8 &&
      v +/- 1e-7 && w +/- 1e-12 && r +/- 1e-8)

    6*v - 0.5 * v * (w*w*r*r) / (1-v) - 2.5
  } ensuring(res => -28.55484 < res && res < 3.822207 && res +/- 8.04865e-6)

  def turbine2(v: Real, w: Real, r: Real): Real = {
    require(-4.5 <= v && v <= -0.3 && 0.4 <= w && w <= 0.9 && 3.8 <= r && r <= 7.8)

    6*v - 0.5 * v * (w*w*r*r) / (1-v) - 2.5
  } ensuring(res => -28.55484 < res && res < 3.822207 && res +/- 1.75704e-13)

  def turbine3Star(v: Real, w: Real, r: Real): Real = {
    require(-4.5 <= v && v <= -0.3 && 0.4 <= w && w <= 0.9 && 3.8 <= r && r <= 7.8 &&
      v +/- 1e-7 && w +/- 1e-12 && r +/- 1e-8)

    3 - 2/(r*r) - 0.125 * (1+2*v) * (w*w*r*r) / (1-v) - 0.5
  } ensuring(res => 0.571726 < res && res < 11.4272 && res +/- 3.349163e-6)

  def turbine3(v: Real, w: Real, r: Real): Real = {
    require(-4.5 <= v && v <= -0.3 && 0.4 <= w && w <= 0.9 && 3.8 <= r && r <= 7.8)

    3 - 2/(r*r) - 0.125 * (1+2*v) * (w*w*r*r) / (1-v) - 0.5
  } ensuring(res => 0.571726 < res && res < 11.4272 && res +/- 8.49925e-14)

  def verhulstStar(r: Real, K: Real, x: Real): Real = {
    require(r >= 4.0 && r <= 4.0 && K >= 1.11 && K <= 1.11 && 0.1 <= x && x <= 0.3 &&
      r +/- 0.001 && K +/- 1e-5 && x +/- 1e-6)

    (r*x) / (1 + (x/K))

  } ensuring(res => 0.3148936 < res && res < 1.1008265 && res +/- 0.000281)

  def verhulst(r: Real, K: Real, x: Real): Real = {
    require(r >= 4.0 && r <= 4.0 && K >= 1.11 && K <= 1.11 && 0.1 <= x && x <= 0.3)

    (r*x) / (1 + (x/K))

  } ensuring(res => 0.3148936 < res && res < 1.1008265 && res +/- 6.81785e-16)

  /*def predatorPreyStar(r: Real, K: Real, x: Real): Real = {
    require(r >= 4.0 && r <= 4.0 && K >= 1.11 && K <= 1.11 && 0.1 <= x && x <= 0.3 &&
      r +/- 0.001 && K +/- 1e-5 && x +/- 1e-6)

    (r*x*x) / (1 + (x/K)*(x/K))

  } ensuring(res => 0.039677 <= res && res <= 0.335495 && res +/- 9.2168e-4)
  */
  def predatorPrey(r: Real, K: Real, x: Real): Real = {
    require(r >= 4.0 && r <= 4.0 && K >= 1.11 && K <= 1.11 && 0.1 <= x && x <= 0.3)

    (r*x*x) / (1 + (x/K)*(x/K))

  } ensuring(res => 0.0396779 < res && res < 0.335494 && res +/- 2.9353123e-16)

  def carbonGasStar(T: Real, a: Real, b: Real, N: Real, p: Real, V: Real): Real = {
    require(T >= 300 && T <= 300 && a >= 0.401 && a <= 0.401 && b >= 42.7e-6 && b <= 42.7e-6 && N >= 1000 && N <= 1000 &&
    p >= 3.5e7 && p <= 3.5e7 && 0.1 <= V && V <= 0.5 && T +/- 0.01 && a +/- 1e-6 && b +/- 1e-10 && N +/- 5 && p +/- 1e-13 && V +/- 0.005)

    val k = 1.3806503e-23
    (p + a * (N / V) * (N / V)) * (V - N * b) - k * N * T

  } ensuring(res => 4303229.99 < res && res <= 16739009.21 && res +/- 2114297.83595)

  def carbonGas(T: Real, a: Real, b: Real, N: Real, p: Real, V: Real): Real = {
    require(T >= 300 && T <= 300 && a >= 0.401 && a <= 0.401 && b >= 42.7e-6 && b <= 42.7e-6 && N >= 1000 && N <= 1000 &&
    p >= 3.5e7 && p <= 3.5e7 && 0.1 <= V && V <= 0.5)

    val k = 1.3806503e-23
    (p + a * (N / V) * (N / V)) * (V - N * b) - k * N * T

  } ensuring(res => 4303229.99 < res && res <= 16739009.21 && res +/- 4.6347106e-8)

  def sine(x: Real): Real = {
    require(x > -1.57079632679 && x < 1.57079632679)
    x - (x*x*x)/6.0 + (x*x*x*x*x)/120.0 - (x*x*x*x*x*x*x)/5040.0 
  } ensuring(res => -0.9998435 < res && res < 0.9998435 && res +/- 9.5541e-16)

  def sqroot(x: Real): Real = {
    require(x >= 0.0 && x < 1.0)
    1.0 + 0.5*x - 0.125*x*x + 0.0625*x*x*x - 0.0390625*x*x*x*x
  } ensuring(res => 0.9999999 < res && res < 1.398438 && res +/- 8.4047352e-16)

  def sineOrder3(x: Real): Real = {
    require(-2.0 < x && x < 2.0)
    0.954929658551372 * x -  0.12900613773279798*(x*x*x)
  } ensuring(res => -1.00000001 < res && res < 1.0000001 && res +/- 1.1079985e-15)

}