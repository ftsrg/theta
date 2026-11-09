// The alloca in one branch gets the same flat address as the malloc in the other. The release at
// return must not free the heap block on the path that skipped the alloca: the block leaks.
#include <stdlib.h>
extern int __VERIFIER_nondet_int(void);

void bad(void) {
  int *data;
  if (__VERIFIER_nondet_int()) {
    data = (int *)malloc(400);
    if (data == 0) abort();
    *data = 5;
  } else {
    data = (int *)__builtin_alloca(400);
    *data = 5;
  }
}

int main(void) {
  bad();
  return 0;
}
