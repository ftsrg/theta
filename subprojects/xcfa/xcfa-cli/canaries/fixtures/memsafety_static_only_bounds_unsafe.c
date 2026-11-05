// Only static objects: the check of a pointer shared between threads still sees the overrun.
typedef unsigned long int pthread_t; extern int pthread_create(pthread_t *t, const void *a, void *(*s)(void *), void *arg); extern int pthread_join(pthread_t t, void **r); extern int __VERIFIER_nondet_int(void);
int a[2];
int b;
int *p = a;
void *w(void *arg) { p = a + 2; return 0; }
int main(void) {
  pthread_t t;
  pthread_create(&t, 0, w, 0);
  pthread_join(t, 0);
  *p = 1;
  return 0;
}
