// The write after the fork does not hide the initial value from the other thread, which runs
// before it.
#include <pthread.h>
extern void abort(void);
void reach_error() {
  abort();
}
int x;
int seen = 1;
void* reader(void* arg) {
  seen = x;
  return 0;
}
int main(void) {
  pthread_t t;
  pthread_create(&t, 0, reader, 0);
  x = 1;
  pthread_join(t, 0);
  if (seen == 0)
    reach_error();
  return 0;
}
