// Exactly one waiter of each round receives PTHREAD_BARRIER_SERIAL_THREAD, over reused rounds.
#include <pthread.h>
extern void abort(void);
void reach_error() { abort(); }

pthread_barrier_t barrier;
int serial[2];

void *worker(void *arg) {
  for (int i = 0; i < 2; i++)
    if (pthread_barrier_wait(&barrier) == -1) serial[i]++; /* PTHREAD_BARRIER_SERIAL_THREAD */
  return 0;
}

int main() {
  pthread_t t1, t2;
  pthread_barrier_init(&barrier, 0, 2);
  pthread_create(&t1, 0, worker, 0);
  pthread_create(&t2, 0, worker, 0);
  pthread_join(t1, 0);
  pthread_join(t2, 0);
  if (serial[0] != 1 || serial[1] != 1) reach_error();
  return 0;
}
