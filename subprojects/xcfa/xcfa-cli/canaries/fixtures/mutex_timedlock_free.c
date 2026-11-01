// timedlock on a free mutex acquires it: it can only time out while the mutex is held.
#include <pthread.h>
extern void abort(void);
void reach_error() { abort(); }
pthread_mutex_t m = PTHREAD_MUTEX_INITIALIZER;
int main() {
  struct timespec ts = {0, 0};
  if (pthread_mutex_timedlock(&m, &ts) != 0) reach_error(); /* free mutex: must succeed */
  return 0;
}
