// A thread's local dies when the thread returns.
typedef unsigned long int pthread_t;
extern int pthread_create(pthread_t* t, const void* a, void* (*s)(void*), void* arg);
extern int pthread_join(pthread_t t, void** r);
extern void pthread_exit(void* r);
extern int __VERIFIER_nondet_int(void);
int fb;
void* wk(void* a) {
  int l = 42;
  int* p = &l;
  return p;
}
int main(void) {
  void* r = &fb;
  pthread_t t;
  pthread_create(&t, 0, wk, 0);
  pthread_join(t, &r);
  return *(int*)r;
}
