int main(int N) {
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
