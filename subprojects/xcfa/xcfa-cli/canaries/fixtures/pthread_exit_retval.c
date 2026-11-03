// pthread_exit's argument is the thread's result, as if the routine returned it.
#include <pthread.h>
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *);
void reach_error() { __assert_fail("0", "pthread_exit_retval.c", 5, "reach_error"); }
int g = 1;
void *thr(void *arg) {
  if (arg) pthread_exit(&g);
  return 0;
}
int main() {
  void *res = 0;
  pthread_t t;
  pthread_create(&t, 0, thr, &g);
  pthread_join(t, &res);
  if (res != &g) reach_error();
  return 0;
}
