// Planted bug: with handles that hold thread ids, the last thread is not joined, so its write may
// come after the check.
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *);
void reach_error() { __assert_fail("0", "pthread_join_runtime_handle_unsafe.c", 6, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
#include <pthread.h>
int data[3];
void *worker(void *arg) {
  data[(int)arg] = 1;
  return 0;
}
int main() {
  int n = __VERIFIER_nondet_int();
  if (n < 1 || n > 3) return 0;
  pthread_t t[3];
  for (int i = 0; i < n; i++) pthread_create(&t[i], 0, worker, (void *)i);
  for (int i = 0; i + 1 < n; i++) pthread_join(t[i], 0);
  if (data[n - 1] != 1) reach_error();
  return 0;
}
