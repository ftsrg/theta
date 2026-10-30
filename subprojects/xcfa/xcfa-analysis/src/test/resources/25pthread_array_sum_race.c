// Same as 12pthread_array_race.c, but the handle is passed as `t + i` -- the pointer-arithmetic
// spelling of `&t[i]`, which must key the same per-element handle.
typedef unsigned long int pthread_t;
typedef union {
  char __size[36];
  long int __align;
} pthread_attr_t;
extern int pthread_create(pthread_t *__newthread, const pthread_attr_t *__attr,
                          void *(*__start_routine)(void *), void *__arg);
extern int pthread_join(pthread_t __th, void **__thread_return);

int g;

void *run(void *arg) {
  g++;
  return 0;
}

int main(void) {
  pthread_t t[2];
  for (int i = 0; i < 2; i++) pthread_create(t + i, 0, run, 0);
  for (int i = 0; i < 2; i++) pthread_join(t[i], 0);
  return 0;
}
