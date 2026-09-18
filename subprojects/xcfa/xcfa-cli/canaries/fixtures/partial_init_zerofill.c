// C11 6.7.9p21: an aggregate with fewer initializers than members has the rest
// zero-initialised. The *local* path used to write only the cells the braces named
// and leave the remainder unconstrained, so the solver could invent any value for
// them -- a false alarm on every `float w[N] = {0}` weight table.
extern void abort(void);
void reach_error() { abort(); }

int main() {
  int a[4] = {1};
  char c[8] = {'a', 'b'};
  struct P {
    int x;
    int y;
  } p[2] = {{1, 2}};
  if (a[0] != 1 || a[1] != 0 || a[2] != 0 || a[3] != 0) reach_error();
  if (c[0] != 'a' || c[1] != 'b' || c[2] != 0 || c[7] != 0) reach_error();
  if (p[0].x != 1 || p[0].y != 2 || p[1].x != 0 || p[1].y != 0) reach_error();
  return 0;
}
