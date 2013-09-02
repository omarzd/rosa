import leon.Real
import Real._

/*
  Benchmarks collected at the 3rd NSV workshop.
  http://www.lix.polytechnique.fr/Labo/Sylvie.Putot/NSV3/
*/
object NSV3 {

  def absorption = {
    float x,y,z;
    int a;

    x = 1;
    y = 0.00000001;

    a = (int) x+y;
    x = x + y;
    z = x - a;
  }

  def middle = {
    int32_t a,b,c,d;

    //a and b in [0,2^(31)-1]

    c = a + b;
    c = c / 2;

    d = b - a;
    d = d / 2;
    d = d + a;
  }

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

  def associativity = {
    double x,y,z,t,u;
    // x,y in [-1000,1000]
    z = x+y;
    t = z-x;
    u = t-y;
  }

  def normalization = {
    double x, y, resx, resy, res;
    // x in [1,2]
    // y in [0.1,0.2]
    resx = y/x;
    resx = 1.0/(sqrt(1.0+resx*resx));
    resy = x/y;
    resy = 1.0/(sqrt(resy*resy+1.0));
    res = resx*resx+resy*resy;
  }

  def polynomial = {
    float x,y,z,t;

    // x in [0,1]
    y = (x-1)*(x-1)*(x-1)*(x-1);
    z = x*x;
    z = z*z - 4*x*z + 6*z - 4*x + 1;
    t = z-y;
  }

  def interpolationA = {
    typedef struct 
    {
      float x;
      float y;
    } paire;

    float main(float E)
    {
      paire T[3];
      float U[3];
      float res;

      U[0] = 3;
      U[1] = 1.45;
      U[2] = 0.2;

      T[0].x = 0.1;
      T[1].x = 5.8;
      T[2].x = 32;

      T[0].y = 0;
      T[1].y = T[1].x * U[0];
      T[2].y = T[1].y + (T[2].x - T[1].x) * U[1];
      

      // E in [0,100]

      if (E < T[1].x)
        res = (E-T[0].x)*U[0] + T[0].y;
      else if (E < T[2].x)
        res = (E-T[1].x)*U[1] + T[1].y;
      else
        res = (E-T[2].x)*U[2] + T[2].y;

      return res;
    }
  }

  def interpolationB = {
    typedef struct 
    {
      float x;
      float y;
    } paire;

    float main(float E)
    {
      paire T[3];
      float U[3];
      int compteur;

      U[0] = 3;
      U[1] = 1.45;
      U[2] = 0.2;

      T[0].x = 0.1;
      T[1].x = 5.8;
      T[2].x = 32;

      T[0].y = 0;
      T[1].y = T[1].x * U[0];
      T[2].y = T[1].y + (T[2].x - T[1].x) * U[1];
      

      // E in [0,100]

      compteur = 0;
      while ((compteur<3) && (E >= T[compteur+1].x))
        compteur++;

      return (E-T[compteur].x)*U[compteur] + T[compteur].y;
    }
  }

  def inversion = {
    #define epsilon 0.001

    void main() {
      double xi, xsi, A, temp;
      signed int *PtrA, *Ptrxi;
      int cond, i, exp, j;

      /* value from which we want to take the inverse */
      // A in [20,30] 

      /* initial condition */  
      PtrA  = (signed int *) (&A);
      Ptrxi = (signed int *) (&xi);
      exp   = (signed int) ((PtrA[0] & 0x7FF00000) >> 20) - 1023;
      xi    = 1;
      Ptrxi[0] = ((1023-exp) << 20);

      cond = 1; 
      i = 0;

      while (cond) {
        xsi = 2*xi-A*xi*xi;
        temp = xsi-xi;
        cond = ((temp > epsilon) || (temp < -epsilon));
        xi = xsi;
        i++;
      }

    }
  }

  def filter = {
    double S,S0,S1,E,E0,E1;
    int i,j;
    
    S = 0.0;
    S0= 0.0;
    S1= 0.0;
    // N in [10,100]

    for (i=1;i<N;i++) {
      E1 = E0;
      E0 = E;
      // E in [-1,1]
      S1 = S0;
      S0 = S;
      S  = 0.7*E - 1.3*E0 + 1.1*E1 + 1.4*S0 - 0.7*S1; 
    }

  }

  def cav10(x: Real): Real = {
    require(x.in(0, 10)) // x in [0,10]
    val y = x*x - x
    if (y >= 0) {
      x/10
    } else {
      x*x + 2
    }
  } ensuring(res => 0 <= res && res <= 3.0)


  def sumOfSixNumbers = {
    #include<stdio.h>

    int main()
      {
      double summands[6];
      double sum = 0.75, sum_bottom_up, sum_top_down;
      int i;

      summands[0] = 5.0 * 64.0 * 33554432.0 * 33554432.0 * 33554432.0 * 33554432.0; /*pow(2,108) + pow(2,106) = (2^2+1) * * 2^6 * 2^25 * 2^25 * 2^25 * 2^25; */
      summands[1] = 2.0 * 67108864.0 * 67108864.0; /* pow(2,52) = 2^26 squared; */
      summands[2] = -summands[0];
      summands[3] = summands[1];
      summands[4] = 0.75;
      summands[5] = -2.0 * summands[1];

    for(i=0; i<6; i++)
      printf("summands[%d] = %15.2e\n", i, summands[i]);

      printf("exact sum = %15.2f\n", sum);

      sum_bottom_up = 0.0;
      for(i=5; i>=0; i--)
        sum_bottom_up += summands[i];
      printf("sum bottom up   = %15.2e\n", sum_bottom_up);

      sum_top_down = 0.0;
      for(i=0; i<6; i++)
        sum_top_down += summands[i];
      printf("sum top down    = %15.2e\n", sum_top_down);

      return 0;
      }
  }

  def letsCountToSix = {
    double one, two, three, four, five, six;
    double pi;
    int i, fin;

    one = 2.0 - 1.0;
    printf("one   = %2.16f\n", one);

    pi = 4.0*atan(1.0);
    /* printf ( " Value of PI = %2.16f \n\n", pi ); */

    two = pow ( 1.0/(cos (100.0*pi+pi/4)), 2.0);
    printf("two   = %2.16f\n", two);

    three = 3.0*tan(atan(100000000.0))/100000000.0;
    printf("three = %2.16f\n", three);

    four = 4.0;
    for (i=0; i<20; i++)
      four = sqrt(four);
    for (i=0; i<20; i++)
      four *= four; 
    printf("four  = %2.16f\n", four);

    five = 5.0 * ((1.0 + exp(-100.0)) - 1.0) / ((1.0 + exp(-100.0)) - 1.0) ;
    printf("five  = %2.16f\n", five);

    six = log (exp(6000.0))/1000.0;
    printf("six   = %2.16f\n", six);

    return 0;
  }

  def integration = {
    #include<stdio.h>
    #include <math.h>

    /* Numerical integration of the integral from 1 to 2 */
    /* of the function 1/x: the exact value is ln 2      */
    /* Integration ??? */
    /* with various choices of the discretization step h */

    int main()
      {
      float xnp1, xn, tn, h, ln2;
      int nb_steps, i;

      ln2 = log(2.0); /* exact value */

      nb_steps = 1;
      while (nb_steps <= 1073741824)
      {
        h = 1.0 / (double)(nb_steps);

        tn=1.0; xn=0.0;
        for (i=0; i<nb_steps; i++)
        {
          xnp1 = xn + h/tn;
          tn += h; xn = xnp1;
        }

        printf("Nb steps = %d, step size = %2.15f, error = %2.15f\n", nb_steps, h, ln2 - xn);
        if (nb_steps< 1073741824) nb_steps *=2; else nb_steps+=1;
      }

      return 0;
      }
  }

  def rumpsFormula = {
    double a, b, res, exact;

    exact = -0.827396059946821; /* −0. 827396059946821368141165095479816 */

    a = 77617.0;
    b = 33096.0;

    res = 333.75 * (b*b*b*b*b*b) + (a*a)*(11.0*a*a*b*b - b*b*b*b*b*b - 121.0*b*b*b*b -2.0) + 5.5*b*b*b*b*b*b*b*b + a/(2.0*b);

    printf("exact = %2.15f   and   res = %2.15f\n", exact, res);

    return 0;
  }

  def mullersSequence = {
    #include<stdio.h>

    /* Muller suite: three fixed points: 3, 5 and 100    */
    /* 3 and 5 are repulsive, 100 is attractive          */
    /* roundoff errors when computing the first terms    */
    /* induce a change from a trajectory converging to 5 */
    /* to a trajectory converging to 100.                */

    int main()
      {
      double xnm1, xn, xnp1;
      int i, fin;

      xnm1=4.0;
      xn=4.25;
      printf("Enter the final index: ");
      scanf("%d", &fin);

      for (i=2; i<= fin; i++)
        {
        xnp1 = 108.0 - (815.0 - 1500.0/xnm1)/xn;
        xnm1 = xn;
        xn = xnp1;
        printf("x[%d] = %f\n", i, xnp1);
        }

      /* printf("x[%d] = %f\n", fin, xnp1); */

      return 0;
      }
  }

  def dekker = {
    /*@ requires xy == \round_double(\NearestEven,x*y) && 
      @          \abs(x) <= 0x1.p995 && 
      @          \abs(y) <= 0x1.p995 &&
      @          \abs(x*y) <=  0x1.p1021;
      @ ensures  ((x*y == 0 || 0x1.p-969 <= \abs(x*y)) 
      @                 ==> x*y == xy+\result);
      @*/
    double Dekker(double x, double y, double xy) {

      double C,px,qx,hx,py,qy,hy,tx,ty,r2;
      int i;
      C=1;
      /*@ loop invariant C== \pow(2., i) && 0 <= i <= 27;
        @ loop variant (27-i); */
      for (i=0; i<27; i++) 
        C*=2;
      C++;
      /*@ assert C == \pow(2.,i) + 1. && i==27; */

      px=x*C;
      qx=x-px;
      hx=px+qx;
      tx=x-hx;

      py=y*C;
      qy=y-py;
      hy=py+qy;
      ty=y-hy;

      r2=-xy+hx*hy;
      r2+=hx*ty;
      r2+=hy*tx;
      r2+=tx*ty;
      return r2;
    }
  }

  def discriminant = {
    /*@ axiomatic FP_ulp {
    @ logic real ulp(double f);
    @
    @ axiom ulp_normal1 :
    @   \forall double f; 0x1p-1022 <= \abs(f) 
    @       ==>\abs(f) < 0x1.p53 * ulp(f) ;
    @
    @ axiom ulp_normal2 :
    @   \forall double f; 0x1p-1022 <= \abs(f) 
    @       ==> ulp(f) <= 0x1.p-52 * \abs(f);
    @ axiom ulp_subnormal :
    @   \forall double f; \abs(f) <  0x1p-1022
    @       ==> ulp(f) == 0x1.p-1074;
    @ axiom ulp_pow :
    @   \forall double f; \exists integer i; 
    @         ulp(f) == \pow(2.,i);
    @ } */


    /*@ ensures \result==\abs(f); */
    double fabs(double f);


    /*@ requires xy == \round_double(\NearestEven,x*y) && 
      @          \abs(x) <= 0x1.p995 && 
      @          \abs(y) <= 0x1.p995 &&
      @          \abs(x*y) <=  0x1.p1021;
      @ ensures  ((x*y == 0 || 0x1.p-969 <= \abs(x*y)) 
      @                 ==> x*y == xy+\result);
      @*/
    double Dekker(double x, double y, double xy);



    /* If no Underflow occur, the result is within 2 ulps 
       of the correct result */

    /*@ requires 
      @     (b==0.   || 0x1.p-916 <= \abs(b*b)) &&
      @     (a*c==0. || 0x1.p-916 <= \abs(a*c)) &&
      @     \abs(b) <= 0x1.p510 && \abs(a) <= 0x1.p995 && \abs(c) <= 0x1.p995 && 
      @     \abs(a*c) <= 0x1.p1021;
      @ ensures \result==0.  || \abs(\result-(b*b-a*c)) <= 2.*ulp(\result);
      @ */


    double discriminant(double a, double b, double c) {
      double p,q,d,dp,dq;
      p=b*b;
      q=a*c;
      
      if (p+q <= 3*fabs(p-q))
        d=p-q;
      else {
        dp=Dekker(b,b,p);
        dq=Dekker(a,c,q);
        d=(p-q)+(dp-dq);
      }
      return d;
    }
  }

  def epsLine1 = {
    #pragma JessieIntegerModel(math)

    //@ logic integer l_sign(real x) = (x >= 0.0) ? 1 : -1;

    /*@ requires e1<= x-\exact(x) <= e2;   
      @ ensures  (\result != 0 ==> \result == l_sign(\exact(x))) &&
      @          \abs(\result) <= 1 ;
      @*/
    int sign(double x, double e1, double e2) {
      
      if (x > e2)
        return 1;
      if (x < e1)
        return -1;
      return 0;
    }
     
    /*@ requires 
      @   sx == \exact(sx)  && sy == \exact(sy) &&
      @   vx == \exact(vx)  && vy == \exact(vy) &&
      @   \abs(sx) <= 100.0 && \abs(sy) <= 100.0 && 
      @   \abs(vx) <= 1.0   && \abs(vy) <= 1.0; 
      @ ensures
      @    \result != 0 
      @      ==> \result == l_sign(\exact(sx)*\exact(vx)+\exact(sy)*\exact(vy))
      @            * l_sign(\exact(sx)*\exact(vy)-\exact(sy)*\exact(vx));
      @*/

    int eps_line(double sx, double sy,double vx, double vy){
      int s1,s2;

      s1=sign(sx*vx+sy*vy, -0x1p-45, 0x1p-45);
      s2=sign(sx*vy-sy*vx, -0x1p-45, 0x1p-45);
     
      return s1*s2;
    }

    /* 
    Local Variables:
    compile-command: "LC_ALL=C make eps_line"
    End:
    */
  }

  def malcom = {
    /*@ ensures \result == 2.; */

    double malcolm1() {
      double A, B;
      A=2.0;
      /*@ ghost int i = 1; */

      /*@ loop invariant A== \pow(2.,i) && 
        @          1 <= i <= 53;
        @ loop variant (53-i); */

      while (A != (A+1)) {
        A*=2.0;
        /*@ ghost i++; */
      }

      /*@ assert i==53 && A== 0x1.p53; */

      B=1;
      /*@ ghost i = 1;*/ 

     /*@ loop invariant B== i && (i==1 || i == 2);
       @ loop variant (2-i); */
      
      while ((A+B)-A != B) {
        B++;
        /*@ ghost i++; */
      }

      return B;

    }
  }

  def sterbenz = {
    /*@ requires  y/2. <= x <= 2.*y;
      @ ensures   \result == x-y;
      @*/

    float Sterbenz(float x, float y) {
      return x-y;
    }
  }

  def recLin2 = {
    
    /*@ axiomatic MKP {
      @  predicate mkp(double uc, double up, integer n);
      @ } */

    // logic real I2R(integer i);



    /*@ requires 2 <= N <= \pow(2,26) && 
      @      \exact(u0)==u0 && \exact(u1)==u1 &&
      @      \forall integer k; 0 <= k <= N ==>  \abs(u0+k*(u1-u0)) <= 1;
      @ ensures  \exact(\result)==u0+N*(u1-u0) &&
      @          \round_error(\result) <= N*(N+1.)/2.*\pow(2,-53);
      @*/


    double comput_seq(double u0, double u1, int N) {
      int i;
      double uprev, ucur,tmp;
      uprev=u0;
      ucur=u1;

      /*@ loop invariant 2 <= i && i <= N+1 && 
        @   \exact(ucur) ==u0+(i-1)*(u1-u0) &&
        @   \exact(uprev)==u0+(i-2)*(u1-u0) &&
        @   mkp(ucur,uprev,i-2); 
        @ loop variant N-i; */ 
      for (i=2; i<=N; i++) {
        tmp=2*ucur;
        /*@ assert tmp==2.*ucur; */
        tmp-=uprev;
        uprev=ucur;
        ucur=tmp;
      }
      return ucur;
    }
  }
}