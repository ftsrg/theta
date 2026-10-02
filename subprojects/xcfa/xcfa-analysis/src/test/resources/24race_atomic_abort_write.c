// The write on the aborting branch of the atomic block races with the other thread's write.
typedef unsigned long int pthread_t;
extern int pthread_create(pthread_t *thread, const void *attr, void *(*start)(void *), void *arg);
extern int __VERIFIER_nondet_int(void);
extern void abort(void);

int x = 0;

void __VERIFIER_atomic_reset(int c) {
  if (c) {
    x = 0;
    abort();
  }
}

void *t(void *arg) {
  x = 1;
  return 0;
}

int main(void) {
  pthread_t th;
  pthread_create(&th, 0, t, 0);
  __VERIFIER_atomic_reset(__VERIFIER_nondet_int());
  return 0;
}
