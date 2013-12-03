
/*
  Benchmarks collected at the 3rd NSV workshop.
  http://www.lix.polytechnique.fr/Labo/Sylvie.Putot/NSV3/
*/

object GoldenNumber {

  def goldenNumberA = {
    float t;
    int i,n;
    t=1;
    // n in [1,1000]
    for (i=1; i<=n; i++) {
      t=t*(sqrt(5)-1)/2;
      t = FPRINT(t);
    } 
    FPRINT(t);
  }

  def goldenNumberB = {
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
  }
  
}