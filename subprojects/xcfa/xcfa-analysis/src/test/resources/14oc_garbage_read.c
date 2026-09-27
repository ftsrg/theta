// The thread reads the never-written a[1] of a heap block, i.e. the initial memory garbage, which
// may be 7. OC must not rule out that read just because main writes a[0] of the same block.
typedef unsigned long int pthread_t;
extern int pthread_create(pthread_t *__newthread, const void *__attr,
                          void *(*__start_routine)(void *), void *__arg);
extern int pthread_join(pthread_t __th, void **__thread_return);
extern void *malloc(unsigned long);
extern void abort(void);
void reach_error() {}

int *a;

void *run(void *arg) {
  if (a[1] == 7) reach_error();
  return 0;
}

int main(void) {
  a = malloc(2 * sizeof(int));
  if (a == 0) abort();
  a[0] = 5;
  pthread_t t;
  pthread_create(&t, 0, run, 0);
  pthread_join(t, 0);
  return 0;
}
