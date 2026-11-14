// The two threads write different cells, but the indices come from a library call that is only
// havocked: the race that a colliding index gives is not reported as real.
#include <pthread.h>
extern int ffs(int);
int data[32];
void *worker(void *arg) {
  data[(int)arg] = 1;
  return 0;
}
int main() {
  pthread_t t1, t2;
  int a = ffs(1) - 1;
  int b = ffs(2) - 1;
  pthread_create(&t1, 0, worker, (void *)a);
  pthread_create(&t2, 0, worker, (void *)b);
  pthread_join(t1, 0);
  pthread_join(t2, 0);
  return 0;
}
