// The racing write only happens after the loop iterated exactly 4 times, beyond the initial bound.
typedef unsigned long int pthread_t;
extern int pthread_create(pthread_t *thread, const void *attr, void *(*start)(void *), void *arg);
extern int pthread_join(pthread_t thread, void **ret);
extern int __VERIFIER_nondet_int(void);

int x;

void *t(void *arg) {
  int i = 0;
  while (__VERIFIER_nondet_int()) i++;
  if (i == 4) x = 1;
  return 0;
}

int main(void) {
  pthread_t th;
  pthread_create(&th, 0, t, 0);
  x = 2;
  pthread_join(th, 0);
  return 0;
}
