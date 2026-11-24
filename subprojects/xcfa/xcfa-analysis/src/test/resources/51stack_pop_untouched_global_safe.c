// f never writes k, so a stack-covered call to f can be popped without losing k.
//
// Without popping, the recursion in f (taken whenever g is not tracked) unrolls forever.
extern void abort(void);
void reach_error() { abort(); }

int g;
int k;

void f(void) {
  if (g > 5) f();
  g = g + 1;
}

void h(void) { f(); }

int main(void) {
  k = 0;
  g = 0;
  f();
  g = 0;
  h();
  if (k != 0) reach_error();
  return 0;
}
