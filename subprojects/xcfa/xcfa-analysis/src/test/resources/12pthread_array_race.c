// Threads created and joined through an array of handles: `pthread_t t[2]` with
// `for (i) pthread_create(&t[i], …)` / `for (i) pthread_join(t[i], …)`. Each `&t[i]` / `t[i]` must
// become a distinct thread handle (PthreadArrayHandleUnrollPass unrolls the loops and folds the
// index), so both threads write `g` concurrently -- a data race. If the array handles were conflated
// into one, the second thread would not spawn and the race would be missed.
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
  for (int i = 0; i < 2; i++) pthread_create(&t[i], 0, run, 0);
  for (int i = 0; i < 2; i++) pthread_join(t[i], 0);
  return 0;
}
