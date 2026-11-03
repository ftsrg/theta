// pthread_cond_timedwait may return ETIMEDOUT.
#include <pthread.h>
extern void abort(void);
void reach_error() { abort(); }
pthread_mutex_t m;
pthread_cond_t c;
int main() {
  struct timespec ts = {0, 0};
  pthread_mutex_init(&m, 0);
  pthread_cond_init(&c, 0);
  pthread_mutex_lock(&m);
  if (pthread_cond_timedwait(&c, &m, &ts) == 110) reach_error(); /* ETIMEDOUT */
  pthread_mutex_unlock(&m);
  return 0;
}
