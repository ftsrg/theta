// Each iteration has a live local of its own.
typedef unsigned long int pthread_t;
extern int pthread_create(pthread_t* t, const void* a, void* (*s)(void*), void* arg);
extern int pthread_join(pthread_t t, void** r);
extern void pthread_exit(void* r);
extern int __VERIFIER_nondet_int(void);
int main(void) {
  int s = 0;
  for (int i = 0; i < 3; i++) {
    int x = i;
    int* p = &x;
    *p = 2;
    s += *p;
  }
  return s - 6;
}
