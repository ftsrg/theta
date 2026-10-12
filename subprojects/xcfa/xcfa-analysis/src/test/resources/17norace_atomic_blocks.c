// Both conflicting accesses are in atomic blocks: no race.
typedef unsigned long int pthread_t;
extern int pthread_create(pthread_t *thread, const void *attr, void *(*start)(void *), void *arg);
extern int pthread_join(pthread_t thread, void **ret);
extern void __VERIFIER_atomic_begin(void);
extern void __VERIFIER_atomic_end(void);

int x;

void *t(void *arg) {
  __VERIFIER_atomic_begin();
  x = x + 1;
  __VERIFIER_atomic_end();
  return 0;
}

int main(void) {
  pthread_t th;
  pthread_create(&th, 0, t, 0);
  __VERIFIER_atomic_begin();
  x = x + 2;
  __VERIFIER_atomic_end();
  pthread_join(th, 0);
  return 0;
}
