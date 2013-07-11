/* FEVS: A Functional Equivalence Verification Suite for High-Performance
 * Scientific Computing
 *
 * Copyright (C) 2010, Stephen F. Siegel, Timothy K. Zirkel,
 * University of Delaware
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License as
 * published by the Free Software Foundation; either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301 USA.
 */

import leon.Real
import Real._
import leon.Utils._

/*
This benchmark is inspired from the
FEVS - Functional Equivalence Verification Suite vsl.cis.udel.edu/fevs
*/
object Mean {

  /*
    Computing the mean.
    In the original benchmark, the numbers are read from a file.
  */


  def aspecIsAlwaysLess(y1: Real, y2: Real, y3: Real, y4: Real, y5: Real, y6: Real): Real = {
    require(y1.in(-1200, 1200) && y2.in(-1200, 1200) && y3.in(-1200, 1200) &&
     y4.in(-1200, 1200) && y5.in(-1200, 1200) && y6.in(-1200, 1200))

    meanSpec(y1, y2, y3, y4, y5, y6) - meanImpl(y1, y2, y3, y4, y5, y6)
  } ensuring(res => res <= 0.0001)
  
  
  /*def actualSpecIsAlwaysLess(y1: Real, y2: Real, y3: Real, y4: Real, y5: Real, y6: Real): Boolean = {
    require(y1.in(-1200, 1200) && y2.in(-1200, 1200) && y3.in(-1200, 1200) &&
     y4.in(-1200, 1200) && y5.in(-1200, 1200) && y6.in(-1200, 1200) && roundoff(y1, y2, y3, y4, y5) && roundoff(y6))

    ~meanSpec(y1, y2, y3, y4, y5, y6) <= ~meanImpl(y1, y2, y3, y4, y5, y6)// + 1e-12
  } holds
  */

  def meanSpec(x1: Real, x2: Real, x3: Real, x4: Real, x5: Real, x6: Real): Real = {
    require(x1.in(-1200, 1200) && x2.in(-1200, 1200) && x3.in(-1200, 1200) &&
     x4.in(-1200, 1200) && x5.in(-1200, 1200) && x6.in(-1200, 1200))

    (x1 + x2 + x3 + x4 + x5 + x6) / 6.0
  } ensuring(res => res <= 1200.0 && -1200.0 <= res && res +/- 1e-10)


  def meanImpl(x1: Real, x2: Real, x3: Real, x4: Real, x5: Real, x6: Real): Real = {
    require(x1.in(-1200, 1200) && x2.in(-1200, 1200) && x3.in(-1200, 1200) &&
     x4.in(-1200, 1200) && x5.in(-1200, 1200) && x6.in(-1200, 1200))

    val i1 = x1
    val i2 = (i1 + x2)/2.0
    val i3 = (2*i2 + x3)/3.0
    val i4 = (3*i3 + x4)/4.0
    val i5 = (4*i4 + x5)/5.0
    val i6 = (5*i5 + x6)/6.0
    i6
  } ensuring(res => res <= 1200.0 && -1200.0 <= res && res +/- 1e-10)

  /*def meanInlined(x1: Real, x2: Real, x3: Real, x4: Real, x5: Real, x6: Real): Boolean = {
    require(x1.in(-1200, 1200) && x2.in(-1200, 1200) && x3.in(-1200, 1200) &&
     x4.in(-1200, 1200) && x5.in(-1200, 1200) && x6.in(-1200, 1200))

    val meanSpec = (x1 + x2 + x3 + x4 + x5 + x6) / 6.0

    val i1 = x1
    val i2 = (i1 + x2)/2.0
    val i3 = (2*i2 + x3)/3.0
    val i4 = (3*i3 + x4)/4.0
    val i5 = (4*i4 + x5)/5.0
    val i6 = (5*i5 + x6)/6.0
    val meanImpl = i6

    meanSpec <= meanImpl
  } holds
  */

  /*def invariant1(y1: Real, y2: Real, y3: Real, y4: Real, y5: Real, y6: Real): Boolean = {
    require(y1.in(-1200, 1200) && y2.in(-1200, 1200) && y3.in(-1200, 1200) &&
     y4.in(-1200, 1200) && y5.in(-1200, 1200) && y6.in(-1200, 1200))

    val m1 = meanSpec(y1, y2, y3, y4, y5, y6)
    val m2 = meanImpl(y1, y2, y3, y4, y5, y6)
    ~m1 <= ~m2 + 0.01
  } holds
*/


}





