// The address of the write is only known through a pointer another thread stores: b is written
// although the initial value of the pointer says a.
#include <pthread.h>
extern void abort(void);
void reach_error() {
  abort();
}
int a, b;
int* q = &a;
void* writer(void* arg) {
  q = &b;
  return 0;
}
int main(void) {
  pthread_t t;
  pthread_create(&t, 0, writer, 0);
  *q = 1;
  pthread_join(t, 0);
  if (b == 1)
    reach_error();
  return 0;
}
