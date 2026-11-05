// A block that is never released must still be reported once only heap bases are considered.
#include <pthread.h>
extern void *malloc(unsigned long);
int *g;
void *worker(void *arg) {
  g = malloc(sizeof(int));
  return 0;
}
int main(void) {
  pthread_t t;
  pthread_create(&t, 0, worker, 0);
  pthread_join(t, 0);
  return 0;
}
