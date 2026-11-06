// A local stored through an out-parameter dies at return.
typedef unsigned long int pthread_t;
extern int pthread_create(pthread_t* t, const void* a, void* (*s)(void*), void* arg);
extern int pthread_join(pthread_t t, void** r);
extern void pthread_exit(void* r);
extern int __VERIFIER_nondet_int(void);
void f(int** o) {
  int x = 1;
  *o = &x;
}
int main(void) {
  int* p;
  f(&p);
  return *p;
}
