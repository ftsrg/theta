// A barrier reached through a pointer has no static identity, so it is refused.
#include <pthread.h>

pthread_barrier_t barrier;
pthread_barrier_t *handle = &barrier;

int main() {
  pthread_barrier_init(handle, 0, 1);
  pthread_barrier_wait(handle);
  return 0;
}
