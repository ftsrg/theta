// A local of main stays valid for the threads that main joins; returning from main ends them all.
typedef unsigned long int pthread_t;
extern int pthread_create(pthread_t* t, const void* a, void* (*s)(void*), void* arg);
extern int pthread_join(pthread_t t, void** r);
extern int __VERIFIER_nondet_int(void);
void* w(void* arg) {
  *(int*)arg = 1;
  return 0;
}
int main(void) {
  int x = 0;
  pthread_t t;
  pthread_create(&t, 0, w, &x);
  pthread_join(t, 0);
  return x - 1;
}
