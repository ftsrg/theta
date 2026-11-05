// A thread-local variable is one object per thread: refused in multithreaded programs.
typedef unsigned long int pthread_t;
extern int pthread_create(pthread_t *thread, const void *attr, void *(*start)(void *), void *arg);
extern int pthread_join(pthread_t thread, void **ret);

__thread int x;

void *t(void *arg) {
  x = 1;
  return 0;
}

int main(void) {
  pthread_t th;
  pthread_create(&th, 0, t, 0);
  x = 2;
  pthread_join(th, 0);
  return 0;
}
