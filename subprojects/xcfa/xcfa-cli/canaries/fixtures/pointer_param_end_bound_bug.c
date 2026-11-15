// The companion of pointer_param_end_bound.c: the walk up to a one-past-the-end parameter must
// still see every element, so the 3 below the bound is found.
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
  int a[4] = {10, 20, 3, 40};
  if (!all_at_least(&a[1], &a[4], 5)) reach_error(); // a[2] lies inside [&a[1], &a[4])
  return 0;
}
