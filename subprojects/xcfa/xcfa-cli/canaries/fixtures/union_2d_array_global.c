// The elements of a global 2-D array of unions are distinct objects, zero without an initializer
// and holding their own braces with one; its cells used to be zeroed as if they were the data.
extern void abort(void);
void reach_error() { abort(); }

union U {
  int i;
  char c[4];
};

union U g2[2][2];
union U gi[2][2] = {{{.i = 1}, {.c = {2}}}, {{3}}};

int main(void) {
  g2[1][0].i = 4;
  if (g2[0][1].i != 0 || g2[1][0].i != 4) reach_error();
  if (gi[0][0].i != 1 || gi[0][1].i != 2 || gi[1][0].i != 3 || gi[1][1].i != 0) reach_error();
  return 0;
}
