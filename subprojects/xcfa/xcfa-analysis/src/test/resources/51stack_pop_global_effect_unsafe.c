// h's call to f sets g to 1, so reach_error is reached.
//
// f is entered twice in identical states (g == 0) on different stacks: main -> f, then
// main -> h -> f. Stack covering pops the second frame; the pop must account for f's write to g.
extern void abort(void);
void reach_error() { abort(); }

int g;

void f(void) {
  // never taken (g is 0 on every entry); the recursion only keeps f from being inlined
  if (g > 5) f();
  g = g + 1;
}

void h(void) { f(); }

int main(void) {
  g = 0;
  f();
  g = 0;
  h();
  if (g != 0) reach_error();
  return 0;
}
