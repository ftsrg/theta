// A library stub that writes through a pointer argument must produce a memory write the data-race
// instrumentation can see. Thread A writes g through fscanf's pointer argument, thread B writes it
// directly, so this races. If LibraryStubsPass runs after ReferenceElimination the pointee type of
// the folded `&g` is gone and no write is emitted at all, and the race is reported as safe.
extern int fscanf(void *stream, const char *fmt, ...);
#include <pthread.h>
int g = 0;
void *tA(void *_) {
  fscanf(0, "%d", &g);
  return 0;
}
void *tB(void *_) {
  g = 7;
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
