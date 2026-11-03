#include <pthread.h>
int g = 0;
void *writer(void *arg) {
  int *p = &g;
  *p = 1; // target: *p = 1
  return 0;
}
int main(void) {
  pthread_t t;
  pthread_create(&t, 0, writer, 0);
  int v = g; // target: g
  pthread_join(t, 0);
  return v;
}
