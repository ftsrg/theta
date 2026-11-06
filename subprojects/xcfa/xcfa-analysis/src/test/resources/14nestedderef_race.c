// Both threads write `a` at an index read through a pointer (`a[*p]`), and both pointers reach the
// same index: a data race whose aliasing depends on a nested dereference.
typedef unsigned long int pthread_t;
typedef union {
  char __size[36];
  long int __align;
} pthread_attr_t;
extern int pthread_create(pthread_t *__newthread, const pthread_attr_t *__attr,
                          void *(*__start_routine)(void *), void *__arg);
extern int pthread_join(pthread_t __th, void **__thread_return);

int a[2];
int one = 1;
int zero = 0;
int *pone = &one;
int *pzero = &one;

void *thr(void *arg) {
  a[*pone] = 2;
  return 0;
}

int main(void) {
  pthread_t id;
  pthread_create(&id, 0, thr, 0);
  a[*pzero] = 1;
  pthread_join(id, 0);
  return 0;
}
