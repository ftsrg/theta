extern void reach_error(void);
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
int* shared;
void* t(void* a) {
  int* p = shared;
  if (p == &slot)
    reach_error();
  shared = &slot;
  return 0;
}
void* u(void* a) {
  return t(a);
}
int main(void) {
  pthread_t a;
  shared = &slot;
  pthread_create(&a, 0, u, 0);
  pthread_join(a, 0);
  if (shared != &slot)
    reach_error();
  return 0;
}
