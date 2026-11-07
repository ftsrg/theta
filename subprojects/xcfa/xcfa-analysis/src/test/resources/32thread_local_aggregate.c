// A thread-local aggregate has no per-thread copy in multithreaded programs: it is refused.
typedef unsigned long int pthread_t;
extern int pthread_create(pthread_t *thread, const void *attr, void *(*start)(void *), void *arg);
extern int pthread_join(pthread_t thread, void **ret);

__thread int x[2];

void *t(void *arg) {
  x[0] = 1;
  return 0;
}

int main(void) {
  pthread_t th;
  pthread_create(&th, 0, t, 0);
  x[0] = 2;
  pthread_join(th, 0);
  return 0;
}
