// pthread_barrier_wait blocks until `count` threads arrive, so the write is visible after it.
#include <pthread.h>
extern void abort(void);
void reach_error() { abort(); }

pthread_barrier_t barrier;
int x;

void *worker(void *arg) {
  x = 1;
  pthread_barrier_wait(&barrier);
  return 0;
}

int main() {
  pthread_t t;
  pthread_barrier_init(&barrier, 0, 2);
  pthread_create(&t, 0, worker, 0);
  pthread_barrier_wait(&barrier);
  if (x != 1) reach_error();
  return 0;
}
