// An array whose elements are `_Atomic`: every cell is atomic, so concurrent writes to the same
// element are race-free. The element is reached at a (base, offset) whose base is the array's id.
typedef unsigned long int pthread_t;
typedef union {
  char __size[36];
  long int __align;
} pthread_attr_t;
extern int pthread_create(pthread_t *__newthread, const pthread_attr_t *__attr,
                          void *(*__start_routine)(void *), void *__arg);
extern int pthread_join(pthread_t __th, void **__thread_return);

_Atomic int a[4];

void *thr(void *arg) {
  a[1] = 1;
  return 0;
}

int main(void) {
  pthread_t id;
  pthread_create(&id, 0, thr, 0);
  a[1] = 2;
  pthread_join(id, 0);
  return 0;
}
