// Each thread's result is kept apart, also for two threads of one routine on a handle array.
#include <pthread.h>
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *);
void reach_error() { __assert_fail("0", "pthread_join_retval_two.c", 5, "reach_error"); }
int a, b;
pthread_t t[2];
void *thr(void *arg) { return arg; }
int main() {
  void *ra = 0, *rb = 0;
  pthread_create(&t[0], 0, thr, &a);
  pthread_create(&t[1], 0, thr, &b);
  pthread_join(t[1], &rb);
  pthread_join(t[0], &ra);
  if (ra != &a || rb != &b) reach_error();
  return 0;
}
