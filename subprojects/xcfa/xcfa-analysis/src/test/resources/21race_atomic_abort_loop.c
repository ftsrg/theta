// The loop body calls atomic functions that may abort. Unrolling merges the aborts of different
// iterations, i.e., of different atomic blocks, which the checker must not trip over.
typedef unsigned long int pthread_t;
extern int pthread_create(pthread_t *thread, const void *attr, void *(*start)(void *), void *arg);
extern int __VERIFIER_nondet_int(void);
extern void abort(void);

int mutex = 1;
int x = 0;

void assume_abort_if_not(int cond) {
  if (!cond) abort();
}
void __VERIFIER_atomic_acquire(void) {
  assume_abort_if_not(mutex == 1);
  mutex = 0;
}
void __VERIFIER_atomic_release(void) {
  assume_abort_if_not(mutex == 0);
  mutex = 1;
}

void *t(void *arg) {
  while (__VERIFIER_nondet_int()) {
    __VERIFIER_atomic_acquire();
    __VERIFIER_atomic_release();
  }
  x = 1;
  return 0;
}

int main(void) {
  pthread_t th;
  pthread_create(&th, 0, t, 0);
  x = 2;
  return 0;
}
