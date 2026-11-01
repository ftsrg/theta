// An array member of a malloc'd struct is a sub-object under the multi model; accessing it must
// not be reported as an invalid dereference (issue #596).
#include <stdlib.h>

struct S {
  int a[4];
  int b;
};

int main(void) {
  struct S *p = malloc(sizeof(struct S));
  if (!p) return 0;
  p->a[3] = 1;
  p->b = 2;
  free(p);
  return 0;
}
