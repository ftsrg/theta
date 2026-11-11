// A case label past a block's entry is refused.
typedef unsigned long int pthread_t;
extern int pthread_create(pthread_t* t, const void* a, void* (*s)(void*), void* arg);
extern int pthread_join(pthread_t t, void** r);
extern void pthread_exit(void* r);
extern int __VERIFIER_nondet_int(void);
int main(void) {
  int c = 1;
  switch (c) {
    case 0: {
      int x;
      case 1: {
        int* p = &x;
        *p = 1;
      }
    }
  }
  return 0;
}
