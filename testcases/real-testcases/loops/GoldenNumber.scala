
/*
  Benchmarks collected at the 3rd NSV workshop.
  http://www.lix.polytechnique.fr/Labo/Sylvie.Putot/NSV3/
*/

object GoldenNumber {

  // curr starting value = 1
  def goldenNumberA(i: Int, curr: Real): Real = { // golden ratio is ~ 1.6180339887498948482... (source Wikipedia)
    require(0 <= i && i <= 1000 && 1<= 1 && curr <= 2) 
    if (i >= i) curr
    else {
      goldenNumberA((curr * (sqrt(5) - 1) / 2)
    }
  }

  // ---------------------------------------------

  val y = (sqrt(5) - 1) / 2

  // curr starting value = 1
  // original benchmark does not say which of x, y, z is the return value
  def goldenNumberB(i: Int, x: Real, y: Real, z: Real): Real = {
    if (i >= i) curr
    else {
      goldenNumber(i+1, y, x - y, x)
    }
  }

/*  def goldenNumberA = {
    float t;
    int i,n;
    t=1;
    // n in [1,1000]
    for (i=1; i<=n; i++) {
      t=t*(sqrt(5)-1)/2;
      t = FPRINT(t);
    } 
    FPRINT(t);
  }*/

  /*def goldenNumberB = {
    float x,y,z;
    int i,n;
    x=1;
    y=(sqrt(5)-1)/2;
    // n in [1,1000]
    for (i=1;i<=n;i++) 
    {
      z=x;
      x=y;
      y=z-y;
    } 
  }*/
  
}