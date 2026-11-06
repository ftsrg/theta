// An address-taken parameter dies when its function returns.
typedef unsigned long int pthread_t;
extern int pthread_create(pthread_t* t, const void* a, void* (*s)(void*), void* arg);
extern int pthread_join(pthread_t t, void** r);
extern void pthread_exit(void* r);
extern int __VERIFIER_nondet_int(void);
int* f(int a) {
  return &a;
}
int main(void) {
  int* p = f(1);
  return *p;
}
