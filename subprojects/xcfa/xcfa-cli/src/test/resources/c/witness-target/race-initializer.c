#include <pthread.h>
int g = 0;
int out = 0;
void *reader(void *arg) {
  int v = g + 1; // target: g + 1
  return (void *)(long)v;
}
int main(void) {
  pthread_t t;
  pthread_create(&t, 0, reader, 0);
  g = 2; // target: g = 2
  pthread_join(t, 0);
  return 0;
}
