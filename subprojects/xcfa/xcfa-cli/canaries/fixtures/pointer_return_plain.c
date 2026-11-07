// A returned plain pointer stays one value.
typedef unsigned long int pthread_t;
extern int pthread_create(pthread_t* t, const void* a, void* (*s)(void*), void* arg);
extern int pthread_join(pthread_t t, void** r);
extern void pthread_exit(void* r);
extern int __VERIFIER_nondet_int(void);
extern void reach_error(void);
int keys[4];
int* h(void) {
  return keys;
}
int main(void) {
  keys[1] = 7;
  int* q = h();
  if (q[1] != 7)
    reach_error();
  return 0;
}
