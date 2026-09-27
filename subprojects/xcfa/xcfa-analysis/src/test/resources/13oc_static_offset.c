// The thread reads a[i] with a dynamic i in {1, 2}; only a[0] is ever written after initialization,
// so a[i] is 0 and reach_error is reachable. OC must not rule out the reads from the initial writes
// of a[1] / a[2] just because a later write targets a statically different offset.
typedef unsigned long int pthread_t;
extern int pthread_create(pthread_t *__newthread, const void *__attr,
                          void *(*__start_routine)(void *), void *__arg);
extern int pthread_join(pthread_t __th, void **__thread_return);
extern int __VERIFIER_nondet_int(void);
void reach_error() {}

int a[3];

void *run(void *arg) {
  int i = __VERIFIER_nondet_int();
  if (i < 1 || i > 2) return 0;
  if (a[i] == 0) reach_error();
  return 0;
}

int main(void) {
  pthread_t t;
  a[0] = 1;
  pthread_create(&t, 0, run, 0);
  pthread_join(t, 0);
  return 0;
}
