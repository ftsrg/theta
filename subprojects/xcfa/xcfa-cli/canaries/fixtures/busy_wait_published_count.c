// A busy-wait loop whose local count is published to a global after the loop.
//
// The busy-wait collapse may run such a loop once only if nothing it writes is observed. The
// liveness it asked counted an assignment to a global as dead whenever the same thread did not read
// that global again, so `x` looked dead and the loop was collapsed; main can only see `g >= 2` after
// two or more spins, so the error became unreachable (a wrong SAFE). Another thread may read any
// global, so a write to one keeps its operands live.
#include <pthread.h>
extern void reach_error(void);
int flag = 0;
int g = 0;
void *setter(void *arg) { flag = 1; return 0; }
void *spinner(void *arg) {
  int x = 0;
  while (flag == 0) { x = x + 1; }
  g = x;
  return 0;
}
int main(void) {
  pthread_t a, b;
  pthread_create(&b, 0, spinner, 0);
  pthread_create(&a, 0, setter, 0);
  pthread_join(a, 0);
  pthread_join(b, 0);
  if (g >= 2) reach_error();
  return 0;
}
