// The second write does not always execute, so it does not hide the first one from the read.
#include <pthread.h>
extern int __VERIFIER_nondet_int(void);
extern void abort(void);
void reach_error() {
  abort();
}
int x;
int other;
void* reader(void* arg) {
  other = 1;
  return 0;
}
int main(void) {
  pthread_t t;
  pthread_create(&t, 0, reader, 0);
  int c = __VERIFIER_nondet_int();
  x = 1;
  if (c)
    x = 2;
  pthread_join(t, 0);
  if (x == 1)
    reach_error();
  return 0;
}
