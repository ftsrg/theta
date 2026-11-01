// A mutex inside a struct or an array is locked through its cell's address: the lock analysis
// resolves that handle, so a union-typed member keeps it instead of its own base (#602).
#include <pthread.h>
extern void abort(void);
void reach_error() { abort(); }

struct S {
  int pad;
  pthread_mutex_t mu;
};

struct S s;
pthread_mutex_t m[2];
int c = 0;

void *t(void *a) {
  struct S *p = &s;
  pthread_mutex_lock(&p->mu);
  pthread_mutex_lock(&m[1]);
  int v = c;
  c = v + 1;
  pthread_mutex_unlock(&m[1]);
  pthread_mutex_unlock(&p->mu);
  return 0;
}

int main() {
  pthread_t x, y;
  pthread_create(&x, 0, t, 0);
  pthread_create(&y, 0, t, 0);
  pthread_join(x, 0);
  pthread_join(y, 0);
  if (c != 2) reach_error();
  return 0;
}
