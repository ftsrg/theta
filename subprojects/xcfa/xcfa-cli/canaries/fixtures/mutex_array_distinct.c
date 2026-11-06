// Distinct mutex array elements protect independent critical sections.
extern void abort(void);
void reach_error(void) { abort(); }
#include <pthread.h>
pthread_mutex_t m[3];
int x;
void *thr(void *arg) {
  pthread_mutex_lock(&m[0]);
  int t = x;
  x = t + 1;
  pthread_mutex_unlock(&m[0]);
  return 0;
}
int main(void) {
  pthread_t t1;
  pthread_create(&t1, 0, thr, 0);
  pthread_mutex_lock(&m[1]);
  int t = x;
  x = t + 1;
  pthread_mutex_unlock(&m[1]);
  pthread_join(t1, 0);
  if (x != 2) reach_error();
  return 0;
}
