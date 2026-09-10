// `alloca` memory is released when the enclosing function returns -- AllocaFunctionPass has
// always said so in its own doc, and nothing ever emitted the release. `__theta_ptr_size`
// was written once at the allocation and only ever cleared by an explicit `free`, so the
// block stayed live for the rest of the program and a use-after-return was accepted
// (memsafety-ext3/getNumbers1-1, a missed bug).
#include <stdlib.h>

int *make(void) {
  int *a = (int *)alloca(4 * sizeof(int));
  a[0] = 1;
  return a; // a pointer to automatic storage, dead at return
}

int main(void) {
  int *p = make();
  return p[0]; // use-after-return
}
