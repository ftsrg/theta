// The control for 09atomicfield_norace.c: the field is an ordinary `int`, so two concurrent writes
// to it are a genuine data race and must still be reported. Guards against the atomic-cell rule
// swallowing races on non-atomic cells.
typedef unsigned long int pthread_t;
typedef union {
  char __size[36];
  long int __align;
} pthread_attr_t;
extern int pthread_create(pthread_t *__newthread, const pthread_attr_t *__attr,
                          void *(*__start_routine)(void *), void *__arg);
extern int pthread_join(pthread_t __th, void **__thread_return);

struct S {
  int f;
};
struct S s;

void *thr(void *arg) {
  s.f = 1;
  return 0;
}

int main(void) {
  pthread_t id;
  pthread_create(&id, 0, thr, 0);
  s.f = 2;
  pthread_join(id, 0);
  return 0;
}
