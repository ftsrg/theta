// Pthread_exit in main ends its locals while threads run on.
typedef unsigned long int pthread_t;
extern int pthread_create(pthread_t* t, const void* a, void* (*s)(void*), void* arg);
extern int pthread_join(pthread_t t, void** r);
extern void pthread_exit(void* r);
extern int __VERIFIER_nondet_int(void);
void* wk(void* a) {
  pthread_exit(0);
}
void* rd(void* a) {
  *(int*)a = 1;
  return 0;
}
int main(void) {
  int x = 0;
  pthread_t t;
  pthread_create(&t, 0, rd, &x);
  pthread_exit(0);
}
