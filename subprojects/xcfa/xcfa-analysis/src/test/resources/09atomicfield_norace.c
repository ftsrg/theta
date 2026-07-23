// Two threads write the same `_Atomic` struct field concurrently. An access to an atomic cell is
// not a data race, so this is race-free -- even though the struct variable itself is ordinary and
// the field is reached through a (base, offset) dereference whose C type is gone by analysis time.
typedef unsigned long int pthread_t;
typedef union {
  char __size[36];
  long int __align;
} pthread_attr_t;
extern int pthread_create(pthread_t *__newthread, const pthread_attr_t *__attr,
                          void *(*__start_routine)(void *), void *__arg);
extern int pthread_join(pthread_t __th, void **__thread_return);

struct S {
  _Atomic int f;
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
