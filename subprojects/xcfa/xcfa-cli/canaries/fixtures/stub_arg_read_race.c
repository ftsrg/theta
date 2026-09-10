// Stubbing a call must keep the reads of its arguments. Thread A passes the shared variable to
// fprintf, thread B writes it, so this races. If the stub simply replaces the call with a havoc of
// its return value, the argument expression disappears with it and the read is never instrumented.
extern int fprintf(void *stream, const char *fmt, ...);
#include <pthread.h>
int shared = 0;
void *tA(void *_) {
  fprintf(0, "%d", shared);
  return 0;
}
void *tB(void *_) {
  shared = 7;
  return 0;
}
int main() {
  pthread_t a, b;
  pthread_create(&a, 0, tA, 0);
  pthread_create(&b, 0, tB, 0);
  pthread_join(a, 0);
  pthread_join(b, 0);
  return 0;
}
