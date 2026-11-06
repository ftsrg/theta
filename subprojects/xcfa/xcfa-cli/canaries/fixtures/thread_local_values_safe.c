extern void reach_error(void);
extern int __VERIFIER_nondet_int(void);
typedef unsigned long int pthread_t;
union pthread_attr_t {
  char __size[36];
  long int __align;
};
typedef union pthread_attr_t pthread_attr_t;
extern int pthread_create(pthread_t* __restrict __newthread,
                          const pthread_attr_t* __restrict __attr, void* (*__start_routine)(void*),
                          void* __restrict __arg) __attribute__((__nothrow__));
extern int pthread_join(pthread_t __th, void** __thread_return);
static __thread int slot;
int done;
void set(int* p, int v) {
  *p = v;
}
void* t(void* a) {
  if (slot != 0)
    reach_error();
  set(&slot, 1);
  if (slot != 1)
    reach_error();
  return 0;
}
int main(void) {
  pthread_t a, b;
  pthread_create(&a, 0, t, 0);
  pthread_create(&b, 0, t, 0);
  set(&slot, 7);
  pthread_join(a, 0);
  pthread_join(b, 0);
  if (slot != 7)
    reach_error();
  return 0;
}
