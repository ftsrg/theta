#include <pthread.h>
#include <stdlib.h>

struct cell {
  int datum;
  pthread_mutex_t mutex;
};
struct cell *c;

void *worker(void *arg) {
  pthread_mutex_lock(&c->mutex);
  c->datum++;
  pthread_mutex_unlock(&c->mutex);
  return 0;
}

int main(void) {
  c = malloc(sizeof(struct cell));
  if (!c) return 0;
  pthread_mutex_init(&c->mutex, 0);
  c->datum = 0;
  pthread_t thread;
  pthread_create(&thread, 0, worker, 0);
  c->datum++;
  return 0;
}
