// `pthread_create(t + i, ...)` is the pointer-arithmetic spelling of `&t[i]`; each element must
// stay its own thread handle, so joining every `t[i]` waits for every thread.
#include <pthread.h>
extern void abort(void);
void reach_error() { abort(); }
int g[2];
void *f(void *a) { g[(long)a] = 1; return 0; }

int main() {
  pthread_t t[2];
  for (long i = 0; i < 2; i++) pthread_create(t + i, 0, f, (void *)i);
  for (long i = 0; i < 2; i++) pthread_join(t[i], 0);
  if (g[0] + g[1] != 2) reach_error();
  return 0;
}
