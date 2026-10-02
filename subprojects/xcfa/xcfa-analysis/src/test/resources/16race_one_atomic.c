// Only one of the two conflicting accesses is in an atomic block, which does not prevent the race.
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
  x = 2;
  pthread_join(th, 0);
  return 0;
}
