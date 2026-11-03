// The thread's return value is not modelled, so a non-null pthread_join retval is refused.
#include <pthread.h>
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *);
void reach_error() { __assert_fail("0", "pthread_join_retval.c", 4, "reach_error"); }
int g = 1;
void *thr(void *arg) { return &g; }
int main() {
  void *res = 0;
  pthread_t t;
  pthread_create(&t, 0, thr, 0);
  pthread_join(t, &res);
  if (res != 0) reach_error();
  return 0;
}
