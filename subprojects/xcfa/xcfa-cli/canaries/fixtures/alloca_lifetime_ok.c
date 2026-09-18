// The other side of alloca_use_after_return.c: a stack block used entirely within its own
// function is live throughout, and releasing it at the return must not invent a violation.
#include <stdlib.h>
extern void abort(void);
void reach_error() { abort(); }

int sum(void) {
  int *a = (int *)alloca(4 * sizeof(int));
  for (int i = 0; i < 4; i++) a[i] = i;
  int t = 0;
  for (int i = 0; i < 4; i++) t += a[i];
  return t;
}

int main(void) {
  if (sum() != 6) reach_error();
  return 0;
}
