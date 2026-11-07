// An uninitialized integer may take any value: its branches stay feasible.
extern void reach_error(void);
typedef unsigned long int pthread_t;
extern int pthread_create(pthread_t* t, const void* a, void* (*s)(void*), void* arg);
extern int pthread_join(pthread_t t, void** r);
extern int __VERIFIER_nondet_int(void);
extern void* malloc(unsigned long);
int g;
void* w(void* arg) {
  g = 1;
  return 0;
}
int main(void) {
  int x;
  int* p = &x;
  pthread_t t;
  pthread_create(&t, 0, w, 0);
  if (*p == 5)
    reach_error();
  pthread_join(t, 0);
  return 0;
}
