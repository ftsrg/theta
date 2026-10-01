// For a data race check, reach_error is no violation: paths from different unrolled atomic blocks
// share the (event-free) way to the error location, which the checker must not trip over.
typedef unsigned long int pthread_t;
extern int pthread_create(pthread_t *thread, const void *attr, void *(*start)(void *), void *arg);
extern int __VERIFIER_nondet_int(void);
extern void abort(void);
extern void reach_error(void);

int y = 0;

void __VERIFIER_atomic_check(int r) {
  if (r) {
    reach_error();
    abort();
  }
}

void *t(void *arg) {
  while (1) {
    __VERIFIER_atomic_check(y);
  }
  return 0;
}

int main(void) {
  pthread_t th;
  pthread_create(&th, 0, t, 0);
  y = __VERIFIER_nondet_int();
  return 0;
}
