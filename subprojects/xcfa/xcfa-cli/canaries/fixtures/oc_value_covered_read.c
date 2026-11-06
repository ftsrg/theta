// The write in this thread hides the initial value, so the error is unreachable.
#include <pthread.h>
extern void abort(void);
void reach_error() {
  abort();
}
struct cell {
  int value;
  int other;
};
struct cell c;
void* writer(void* arg) {
  c.other = 1;
  return 0;
}
int main(void) {
  pthread_t t;
  c.value = 1;
  pthread_create(&t, 0, writer, 0);
  struct cell* p = &c;
  if (p->value != 1)
    reach_error();
  pthread_join(t, 0);
  return 0;
}
