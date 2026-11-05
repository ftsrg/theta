// After a conditional join, the merged path may run without the join, before the thread's write.
typedef unsigned long int pthread_t;
extern int pthread_create(pthread_t *thread, const void *attr, void *(*start)(void *), void *arg);
extern int pthread_join(pthread_t thread, void **ret);
extern int __VERIFIER_nondet_int(void);
extern void reach_error(void);

int x;

void *t(void *arg) {
  x = 1;
  return 0;
}

int main(void) {
  pthread_t th;
  pthread_create(&th, 0, t, 0);
  if (__VERIFIER_nondet_int()) pthread_join(th, 0);
  if (x == 0) reach_error();
  return 0;
}
