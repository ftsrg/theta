// The previous iteration's local is dead.
typedef unsigned long int pthread_t;
extern int pthread_create(pthread_t* t, const void* a, void* (*s)(void*), void* arg);
extern int pthread_join(pthread_t t, void** r);
extern void pthread_exit(void* r);
extern int __VERIFIER_nondet_int(void);
int main(void) {
  int* p = 0;
  for (int i = 0; i < 2; i++) {
    int x = 1;
    if (i == 1)
      *p = 2;
    p = &x;
  }
  return 0;
}
