// A pointer set on one path only: following it there still reads the other thread's write.
extern void reach_error(void); typedef unsigned long int pthread_t; extern int pthread_create(pthread_t *t, const void *a, void *(*s)(void *), void *arg); extern int pthread_join(pthread_t t, void **r); extern int __VERIFIER_nondet_int(void); extern void *malloc(unsigned long);
int a;
int set(int **out) {
  if (a == 1) { *out = &a; return 1; }
  return 0;
}
void *w(void *arg) { a = 1; return 0; }
int main(void) {
  int *r;
  pthread_t t;
  pthread_create(&t, 0, w, 0);
  if (set(&r)) {
    if (*r == 1) reach_error();
  }
  pthread_join(t, 0);
  return 0;
}
