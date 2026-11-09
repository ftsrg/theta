// A pointer stored in a heap block by another thread is followed to its target.
extern void reach_error(void);
typedef unsigned long int pthread_t;
extern int pthread_create(pthread_t* t, const void* a, void* (*s)(void*), void* arg);
extern int pthread_join(pthread_t t, void** r);
extern int __VERIFIER_nondet_int(void);
extern void* malloc(unsigned long);
struct box {
  int* p;
};
struct box* b;
int v;
void* w(void* arg) {
  v = 1;
  b->p = &v;
  return 0;
}
int main(void) {
  b = malloc(sizeof(struct box));
  if (!b)
    return 0;
  b->p = 0;
  pthread_t t;
  pthread_create(&t, 0, w, 0);
  pthread_join(t, 0);
  if (*b->p == 1)
    reach_error();
  return 0;
}
