
import leon.Real
import Real._

import leon.Utils._

object SinCos {
  

  def fabs(x: Real): Real = {
    if( x < 0) -x
    else x
  }

  def fSqrt(int context, double x) {

    val _C0 = 1.414213538169860839843750
    val _C1 = 0.2297613918781280517578125
    val _C2 = 1.296735525131225585937500
    val _C3 = -0.9010983705520629882812500
    val _C4 = 0.4935534000396728515625000
    val _C5 = -0.1189586669206619262695313125

    _C1+(_C2+(_C3+(_C4+_C5*x)*x)*x)*x
  }


  // The code is supposed to call these functions depending on the range
  // of the input, but the code never calls sin1, sin3 or sin4???

  // This would be a good benchmark for synthesizing those ranges

  def sin1(x: Real): Real = {
    val x2 = x*x
    ((-14.13341245 / (x2+41.17619681)+ 0.176575) * x2 + 1.0) * x
  }

  def sin2(x: Real): Real  = {
    val x2 = x*x
    (((-x2/(6.0*7)+1.0)*x2/(5.0*4)-1.0)*x2/(2.0*3)+1.0)*x
  }

  def sin3(x: Real): Real = {
    val x2 = x*x
    (x2/(x2/(x2/(x2/(x2/-8.6822950335 +9.6717198021)+11.4544368439)+-3.3333337415)+-6.0000000056)+1.0)*x
  }

  def sin4(x: Real): Real = {
    val SS_A0S = 1.0
    val SS_AS = (9.6717198021*-8.6822950335 +-3.3333337415*(11.4544368439 +-8.6822950335))
    val SS_BS = (-3.3333337415*11.4544368439*9.6717198021*-8.6822950335)
    val SS_CS = (-6.0000000056 +11.4544368439 +-8.6822950335)
    val SS_DS = (-6.0000000056*-3.3333337415*(11.4544368439 +-8.6822950335)+(-6.0000000056 +11.4544368439)*9.6717198021*-8.6822950335)
    val SS_ES = (-6.0000000056*-3.3333337415*11.4544368439*9.6717198021*-8.6822950335)

    val x2 = x*x
    ((((x2+SS_AS)*x2+SS_BS)*x2) /((SS_CS*x2+SS_DS)*x2+SS_ES)+SS_A0S)*x
  }

  /*def sincospi2(double x, double *const sinx, double *const cosx){
  double vax,z1;
  int N11, N2, N3, fC;
  double yy1, a;

  if(x < 10.0e-10){
      yy1 = x;
      z1 = F_SQRT(0, (double)(1.0-yy1*yy1));
  }else{
    if(x == 0.785398164){
      yy1 = F_SQRT(1, (double)2.0)/2.0;
      z1 = F_SQRT(2, (double)(1.0-yy1*yy1));
    }else{
      if(x > 0.785398164){
 x = (3.141592654/2.0)-x;
 fC=1;
 z1 = sin2(x);
 yy1 = F_SQRT(3, (double)(1.0-z1*z1));
      }else{
 yy1 = sin2(x);
 z1 = F_SQRT(4, (double)(1.0-yy1*yy1));
      }
    }
  }
  a = x;
  *sinx = yy1;
  *cosx = z1;
}*/

}

/*
double __BUILTIN_DAED_DBETWEEN(double left, double right);

struct SSA {
  double A0S, AS, BS, CS, DS, ES;
};

SSA SS;

struct Test
{
  double ac;
  double s1, c1, ss;
};

double a0,s1,c1;
double s2,c2;
double norme1,norme2;
double s1er, c1er;
double err = 4.0e-7;
int num;
double i1;
double _C0, _C1, _C2, _C3, _C4, _C5;

double fabs(double x){
  if( x < 0)
    return -x;
  else
    return x;
}

double TRUNC( double x){
  int tr;
  tr = x;
  return(tr);
}

double F_SQRT(int context, double x) {

  double res;

  res = _C1+(_C2+(_C3+(_C4+_C5*x)*x)*x)*x;
  return res;
}

double sin1( double x){
  double x2 = x*x;
  return( ((-14.13341245 / (x2+41.17619681)+ 0.176575) * x2 + 1.0) * x);
}

double sin2( double x){
  double x2 = x*x;
  return((((-x2/(6.0*7)+1.0)*x2/(5.0*4)-1.0)*x2/(2.0*3)+1.0)*x);
}

double sin3( double x){
  double x2 = x*x;
  return( (x2/(x2/(x2/(x2/(x2/-8.6822950335 +9.6717198021)+11.4544368439)+-3.3333337415)+-6.0000000056)+1.0)*x );
}

double sin4( double x){
  double x2 = x*x;
  return( ((((x2+SS.AS)*x2+SS.BS)*x2)
    /((SS.CS*x2+SS.DS)*x2+SS.ES)+SS.A0S)*x );
}

void sincospi2(double x, double *const sinx, double *const cosx){
  double vax,z1;
  int N11, N2, N3, fC;
  double yy1, a;

  if(x < 10.0e-10){
      yy1 = x;
      z1 = F_SQRT(0, (double)(1.0-yy1*yy1));
  }else{
    if(x == 0.785398164){
      yy1 = F_SQRT(1, (double)2.0)/2.0;
      z1 = F_SQRT(2, (double)(1.0-yy1*yy1));
    }else{
      if(x > 0.785398164){
 x = (3.141592654/2.0)-x;
 fC=1;
 z1 = sin2(x);
 yy1 = F_SQRT(3, (double)(1.0-z1*z1));
      }else{
 yy1 = sin2(x);
 z1 = F_SQRT(4, (double)(1.0-yy1*yy1));
      }
    }
  }
  a = x;
  *sinx = yy1;
  *cosx = z1;
}

void sincos1(double x, double *const sinx, double *const cosx){
  double vax,z1;
  int N11, N2, N3, fC;
  double yy1, a;
  fC = 0;
  vax = fabs(x);
  if(vax < 1.0e7){
      if (x < 0.0){
        x=vax;
        if(x > 6.283185308)
          x -= TRUNC(x/(2.0*3.141592654))*2.0*3.141592654;
        if(x > 3.141592654){
          x -= 3.141592654;
          if(x > 1.570796327){
            x = 3.141592654 - x;
            sincospi2(x, &yy1, &z1);
        }else{
          sincospi2(x, &yy1, &z1);
          z1 = - z1;
        }
      }else{
        if(x > 1.570796327){
          x = 3.141592654 - x;
          sincospi2(x, &yy1, &z1);
          z1 = - z1;
          yy1 = - yy1;
   }else{
     sincospi2(x, &yy1, &z1);
     yy1 = - yy1;
   }
 }
      }else{
 if(x > 6.283185308)
   x -= TRUNC(x/(2.0*3.141592654))*2.0*3.141592654;
 if(x > 3.141592654){
   x -= 3.141592654;
   if(x > 1.570796327){
     x = 3.141592654 - x;
     sincospi2(x, &yy1, &z1);
     yy1 = - yy1;
   }else{
     sincospi2(x, &yy1, &z1);
     yy1 = - yy1;
     z1 = - z1;
   }
 }else{
   if(x > 1.570796327){
     x = 3.141592654 - x;
     sincospi2(x, &yy1, &z1);
     z1 = - z1;
   }else
     sincospi2(x, &yy1, &z1);
 }
      }
  }else
    yy1 = 9.9e+27;

  a = x;
  *sinx = yy1;
  *cosx = z1;
}

int main(){
  int i;
  double reference;
  double should_be_zero, should_be_zero1, should_be_zero2, should_be_zero3, should_be_zero4, should_be_zero5, should_be_zero6, should_be_zero7, should_be_zero8, should_be_zero9, should_be_zero10, should_be_zero11, should_be_zero12, should_be_zero13, should_be_zero14, should_be_zero15;
  Test test, test1, test2, test3, test4, test5, test6, test7, test8, test9, test10, test11, test12, test13, test14, test15;
  SS.A0S = 1.0;
  SS.AS = (9.6717198021*-8.6822950335 +-3.3333337415*(11.4544368439 +-8.6822950335));
  SS.BS = (-3.3333337415*11.4544368439*9.6717198021*-8.6822950335);
  SS.CS = (-6.0000000056 +11.4544368439 +-8.6822950335);
  SS.DS = (-6.0000000056*-3.3333337415*(11.4544368439 +-8.6822950335)+(-6.0000000056 +11.4544368439)*9.6717198021*-8.6822950335);
  SS.ES = (-6.0000000056*-3.3333337415*11.4544368439*9.6717198021*-8.6822950335);
  _C0 = 1.414213538169860839843750;
  _C1 = 0.2297613918781280517578125;
  _C2 = 1.296735525131225585937500;
  _C3 = -0.9010983705520629882812500;
  _C4 = 0.4935534000396728515625000;
  _C5 = -0.1189586669206619262695313125;
  test.ac = 3.141592654/16.0;
  sincos1(test.ac,&test.s1,&test.c1);
  should_be_zero = test.s1*test.s1+test.c1*test.c1-1.0;
  
  test.ac = 3.0*3.141592654/16.0;
  sincos1(test.ac,&test.s1,&test.c1);
  should_be_zero = test.s1*test.s1+test.c1*test.c1-1.0;
  
  reference = (3.141592654/8.0)/32;
  i = 0;
  while (i < 15) {
     test1.ac = __BUILTIN_DAED_DBETWEEN(3.141592654/16.0+reference*i, 3.141592654/8.0+reference*(i+1));
     sincos1(test1.ac,&test1.s1,&test1.c1);
     should_be_zero1 = test1.s1*test1.s1+test1.c1*test1.c1-1.0;

     test2.ac = __BUILTIN_DAED_DBETWEEN(3.141592654/16.0+reference*(i+0.5), 3.141592654/8.0+reference*(i+1.5));
     sincos1(test2.ac,&test2.s1,&test2.c1);
     should_be_zero2 = test2.s1*test2.s1+test2.c1*test2.c1-1.0;
     ++i;
  };
  i = 0;
  while (i < 15) {
     test1.ac = __BUILTIN_DAED_DBETWEEN(3.141592654/16.0+reference*i, 3*3.141592654/16.0);
     sincos1(test1.ac,&test1.s1,&test1.c1);
     should_be_zero1 = test1.s1*test1.s1+test1.c1*test1.c1-1.0;

     test2.ac = __BUILTIN_DAED_DBETWEEN(3.141592654/16.0+reference*(i+0.5), 3*3.141592654/16.0);
     sincos1(test2.ac,&test2.s1,&test2.c1);
     should_be_zero2 = test2.s1*test2.s1+test2.c1*test2.c1-1.0;
     ++i;
  };
  test3.ac = __BUILTIN_DAED_DBETWEEN(3.141592654/16.0+reference*15.0, 3*3.141592654/16.0);
  sincos1(test3.ac,&test3.s1,&test3.c1);
  should_be_zero3 = test3.s1*test3.s1+test3.c1*test3.c1-1.0;
}

*/