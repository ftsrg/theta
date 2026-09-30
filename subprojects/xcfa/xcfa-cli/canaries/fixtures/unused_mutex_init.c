// Every element of a global mutex array is initialised field by field, through nested
// objects, although nothing reads those fields. The initialisation alone used to make
// the analysis time out; unread writes to global objects are now dropped.
#include <pthread.h>
extern void abort(void);
void reach_error() { abort(); }

pthread_mutex_t m[30];
int x;

void *thr(void *arg) {
  pthread_mutex_lock(&m[0]);
  x++;
  pthread_mutex_unlock(&m[0]);
  return 0;
}

int main() {
  pthread_t t1, t2;
  pthread_create(&t1, 0, thr, 0);
  pthread_create(&t2, 0, thr, 0);
  pthread_join(t1, 0);
  pthread_join(t2, 0);
  if (x != 2) reach_error();
  return 0;
}
