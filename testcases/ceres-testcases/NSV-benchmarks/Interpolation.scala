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


--------------------------------
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