// A pointer parameter compared with a walked pointer keeps the offset its caller binds, here one
// past the end. Splitting the callee before inlining assumed offset 0 for it, so `first != last`
// never held at the end and the walk read past the array.
extern void abort(void);
void reach_error() { abort(); }

static int all_at_least(int *first, int *last, int bound) {
  while (first != last) {
    if (*first < bound) return 0;
    first = &first[1];
  }
  return 1;
}

int main() {
  int a[4] = {10, 20, 30, 40};
  if (!all_at_least((int *)a, &((int *)a)[4], 5)) reach_error();
  return 0;
}
