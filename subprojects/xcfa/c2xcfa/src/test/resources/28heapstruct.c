// Regression: `p->field` through a heap pointer used to emit a double
// dereference (arrays[arrays[p][0]][i]) -- it read field 0's value and used it
// as a base address. Combined with `sizeof(struct S)` silently evaluating to 0
// (unresolvable struct tag -> malloc(0)), every access through a malloc'd
// struct pointer was reported as an invalid dereference.
extern void abort(void);
extern void reach_error(void);
extern void *malloc(unsigned long);

struct S {
  int a;
  int b;
};

int main() {
  struct S *p = malloc(sizeof(struct S));
  if (!p) return 0;
  p->a = 1;
  p->b = 2;
  if (p->a != 1 || p->b != 2) {
    reach_error();
    abort();
  }
  return 0;
}
