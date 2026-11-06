// A thread's locals die when it returns: reading one through its join result is invalid.
#include <pthread.h>
extern void abort(void);

void *worker(void *arg) {
  int local = 42;
  int *p = &local;
  return p;
}

int main() {
  void *res;
  pthread_t t;
  pthread_create(&t, 0, worker, 0);
  pthread_join(t, &res);
  if (*(int *)res != 42) abort();
  return 0;
}
