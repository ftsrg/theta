// A pointer sum stored into a member keeps its offset.
typedef unsigned long int pthread_t;
extern int pthread_create(pthread_t* t, const void* a, void* (*s)(void*), void* arg);
extern int pthread_join(pthread_t t, void** r);
extern void pthread_exit(void* r);
extern int __VERIFIER_nondet_int(void);
extern void reach_error(void);
int keys[4];
struct C {
  int* p;
} c;
int main(void) {
  keys[1] = 7;
  c.p = keys + 1;
  int* q = c.p;
  if (*q != 7)
    reach_error();
  return 0;
}
