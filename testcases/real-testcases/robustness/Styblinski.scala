import leon.real._
import RealOps._
import annotations._

object StyblinskiTang {

  def quadraticFit(x: Real, y: Real): Real = {
    require(-5 <= x && x <= 5 && -5 <= y && y <= 5)// && x +/- 1e-8 && y +/- 1e-8)

    if (y <= 0)
      if (x <= 0)
        44.3803 + 58.375*x + 13.875*x*x + 59.1829*y + 3.19593e-14*x*y + 13.6286*y*y   // x<=0&&y<=0
      else 
        40.5 - 53.375*x + 13.875*x*x + 58.375*y + 13.875*y*y   // x>=0&&y<=0
    else 
      if (x <= 0)
        40.5 + 58.375*x + 13.875*x*x - 53.375*y + 1.65363e-14*x*y + 13.875*y*y   // x<=0&&y>=0
      else 
        40.5 -53.375*x + 13.875*x*x - 53.375*y - 3.54349e-15*x*y + 13.875*y*y   // x>=0&&y>=0
  }

  // this is the styblisnki function a little modified, y^3 instead of y^4
  def quadraticFitNonrectangular(x: Real, y: Real): Real = {
    require(-5 <= x && x <= 5 && -5 <= y && y <= 5)// && x +/- 1e-8 && y +/- 1e-8)

    if (y < x)
      -26.0357 + 2.5*x + 3.69643*x*x + 8.89286*y - 1.95404e-15*x*y - 8.96429*y*y    //y<x
    else
      -37.6071 + 2.5*x + 3.69643*x*x + 8.89286*y + 5.06046e-15*x*y - 7.03571*y*y   //x<y

  }

}