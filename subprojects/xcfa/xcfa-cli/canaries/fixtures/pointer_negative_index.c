// A negative index from a pointer into the middle of an object. Under integer arithmetic the index
// was converted to the unsigned size_t, and the sum, which does not wrap, lay 2^N elements away.
#include <stdlib.h>
extern void abort(void);
void reach_error() { abort(); }
struct S { int a; int b; };
int main() {
  int *b = malloc(2 * sizeof(int));
  if (!b) return 0;
  b[0] = 7;
  b[1] = 8;
  int *p = b + 1;
  int k = -1;
  if (p[-1] != 7 || *(p - 1) != 7 || p[k] != 7) reach_error();
  struct S s[2] = {{1, 2}, {3, 4}};
  struct S *q = &s[1];
  if (q[-1].b != 2 || (q + k)->a != 1) reach_error();
  free(b);
  return 0;
}
