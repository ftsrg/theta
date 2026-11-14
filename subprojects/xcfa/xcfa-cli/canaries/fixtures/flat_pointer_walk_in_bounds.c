// Pointers derived from `a` by arithmetic and copies stay checked against `a` alone, and every
// access here is inside it: the bound must not be taken from the next object, nor be tighter.
int a[4], b[2];

int main(void) {
  int *p = a;
  int s = 0;
  for (int i = 0; i < 4; i++) s += p[i];
  int *q = p + 3;
  s += *q;
  q--;
  s += q[0];
  return s + b[1];
}
