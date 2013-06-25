double __BUILTIN_DAED_DBETWEEN(double left, double right);

double filter(double a, double b, double c, double d, double e) {
  double S, S0, S1, E, E0, E1;
  int i;
  S = 0.0;
  S0 = 0.0;
  S1 = 0.0;
  E = __BUILTIN_DAED_DBETWEEN(-1.0, 0.0);
  E0 = __BUILTIN_DAED_DBETWEEN(-1.0, 0.0);

  i = 1;
  while (i < 20) {
     E1 = E0;
     E0 = E;
     E = __BUILTIN_DAED_DBETWEEN(-1.0, 0.0);
     S1 = S0;
     S0 = S;
     S = a*E - b*E0 + c*E1 + d*S0 - e*S1;
     ++i;
  };
  while (i < 40) {
     E1 = E0;
     E0 = E;
     E = __BUILTIN_DAED_DBETWEEN(0.0, 1.0);
     S1 = S0;
     S0 = S;
     S = a*E - b*E0 + c*E1 + d*S0 - e*S1;
     ++i;
  };
  while (i < 60) {
     E1 = E0;
     E0 = E;
     E = __BUILTIN_DAED_DBETWEEN(-1.0, 0.0);
     S1 = S0;
     S0 = S;
     S = a*E - b*E0 + c*E1 + d*S0 - e*S1;
     ++i;
  };
  while (i < 80) {
     E1 = E0;
     E0 = E;
     E = __BUILTIN_DAED_DBETWEEN(0.0, 1.0);
     S1 = S0;
     S0 = S;
     S = a*E - b*E0 + c*E1 + d*S0 - e*S1;
     ++i;
  };
  while (i < 100) {
     E1 = E0;
     E0 = E;
     E = __BUILTIN_DAED_DBETWEEN(-1.0, 0.0);
     S1 = S0;
     S0 = S;
     S = a*E - b*E0 + c*E1 + d*S0 - e*S1;
     ++i;
  };
  while (i < 120) {
     E1 = E0;
     E0 = E;
     E = __BUILTIN_DAED_DBETWEEN(0.0, 1.0);
     S1 = S0;
     S0 = S;
     S = a*E - b*E0 + c*E1 + d*S0 - e*S1;
     ++i;
  };
  return S;
}

int main() {
  double result, a, b, c, d, e;
  int j;
  result = filter(0.69, 1.31, 1.09, 1.39, 0.71);
  result = filter(0.71, 1.29, 1.11, 1.41, 0.69);

  a = __BUILTIN_DAED_DBETWEEN(0.69, 0.71);
  b = __BUILTIN_DAED_DBETWEEN(1.29, 1.31);
  c = __BUILTIN_DAED_DBETWEEN(1.09, 1.11);
  d = __BUILTIN_DAED_DBETWEEN(1.39, 1.41);
  e = __BUILTIN_DAED_DBETWEEN(0.69, 0.71);

  result = filter(a, 1.3, 1.1, 1.4, 0.7);
  result = filter(0.7, b, 1.1, 1.4, 0.7);
  result = filter(0.7, 1.3, c, 1.4, 0.7);
  result = filter(0.7, 1.3, 1.1, d, 0.7);
  result = filter(0.7, 1.3, 1.1, 1.4, e);
  result = filter(a, b, c, d, e);
  
  result = filter(a, 1.3, 1.1, 1.4, 0.7);
  result = filter(0.7, b, 1.1, 1.4, 0.7);
  result = filter(0.7, 1.3, c, 1.4, 0.7);
  result = filter(0.7, 1.3, 1.1, d, 0.7);
  result = filter(0.7, 1.3, 1.1, 1.4, e);
  result = filter(a, b, c, d, e);
  return 0;
}