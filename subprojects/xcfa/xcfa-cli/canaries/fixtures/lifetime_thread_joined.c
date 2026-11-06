// A local is valid for a thread joined before it dies.
typedef unsigned long int pthread_t;
extern int pthread_create(pthread_t* t, const void* a, void* (*s)(void*), void* arg);
extern int pthread_join(pthread_t t, void** r);
extern void pthread_exit(void* r);
extern int __VERIFIER_nondet_int(void);
void* rd(void* a) {
  *(int*)a = 1;
  return 0;
}
int f(void) {
  int x = 0;
  pthread_t t;
  pthread_create(&t, 0, rd, &x);
  pthread_join(t, 0);
  return x;
}
int main(void) {
  return f() - 1;
}
