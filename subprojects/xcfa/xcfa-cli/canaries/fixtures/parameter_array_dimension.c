// A parameter's outermost array dimension only decays to a pointer. Naming a global (`x[N]`) or
// another parameter (`y[n]`) there made the function unreadable, so it was dropped as unused.
extern void abort(void);
void reach_error() { abort(); }

int N;
int first(int x[N]) { return x[0]; }
int last(int n, int y[n]) { return y[n - 1]; }

int main(void) {
  N = 3;
  int a[3] = {4, 5, 6};
  if (first(a) != 4) reach_error();
  if (last(3, a) != 6) reach_error();
  return 0;
}
