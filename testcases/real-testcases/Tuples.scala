import leon.Real
import Real._


object Tuples {

  // s1, s2, s3, s4, y1, y2: <1, 16, 11>
  /*def out1(s1: Real, s2: Real, s3: Real, s4: Real) = {
    require(-10 <= s1 && s1 <= 10 && -10 <= s2 && s2 <= 10 && -10 <= s3 && s3 <= 10 && -10 <= s4 && s4 <= 10)

    val x1 = (-0.0429) * s1 + (-0.9170) * s2 + (-0.3299) * s3 + (-0.8206) * s4
    val x2 = 2.4908 * s1 + 0.0751 * s2 + 1.7481 * s3 + (-1.1433) * s4
    (x1, x2)
  } ensuring (_ match {
    case (a, b) => a <= 100 && b >= -100 && a +/- 1e-7 && b +/- 1e-8    
  })*/


  def out2(s1: Real, s2: Real, s3: Real, s4: Real) = {
    require(-10 <= s1 && s1 <= 10 && -10 <= s2 && s2 <= 10 && -10 <= s3 && s3 <= 10 && -10 <= s4 && s4 <= 10)

    val x1 = (-0.0429) * s1 + (-0.9170) * s2 + (-0.3299) * s3 + (-0.8206) * s4
    val x2 = 2.4908 * s1 + 0.0751 * s2 + 1.7481 * s3 + (-1.1433) * s4
    f(x1, x2)
  } ensuring (_ match {
    case (a, b) => a <= 100 && b >= -100 && a +/- 1e-7 && b +/- 1e-8    
  }) 

  def f(x1: Real, x2: Real): (Real, Real) = {
    require(-22 <= x1 && x1 <= 22 && -55 <= x2 && x2 <= 55 && x1 +/- 1e-14 && x2 +/- 1e-13)
    (x1, x2)
  } ensuring (_ match {
    case (a, b) => -22 <= a && a <= 22 && -55 <= b && b <= 55 && a +/- 1e-14 && b +/- 1e-13 
  })

  /*ensuring(res => {
    val (a, b) = res
    a <= 100 && b >= -100 && a +/- 1e-7 && b +/- 1e-8    
    })*/

  //ensuring (res => res._1 <= 100 && res._2 >= -100 && res._1 +/- 1e-7 && res._2 +/- 1e-8)
  

/*
(res => {
    val (b,c,l1) = res
    !setA(l1).contains(x)
  })


(_ match {
    case (a, b) => a <= b && Set(a,b) == Set(x,y)
  })
*/
}