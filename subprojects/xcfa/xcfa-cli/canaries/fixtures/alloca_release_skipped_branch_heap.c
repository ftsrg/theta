// The alloca in one branch gets the same flat address as the malloc in the other. The release at
// return must not free the heap block on the path that skipped the alloca: `*g` stays valid.
#include <stdlib.h>
extern int __VERIFIER_nondet_int(void);
int *g;

void f(void) {
  int *p;
  if (__VERIFIER_nondet_int()) {
    g = malloc(sizeof(int));
  } else {
    p = (int *)__builtin_alloca(sizeof(int));
    *p = 1;
  }
}

int main(void) {
  f();
  if (g) {
    *g = 1;
    free(g);
  }
  return 0;
}
