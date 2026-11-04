#include <pthread.h>
int g = 0;
int get(void) {
  return g; // target: g
}
void *reader(void *arg) {
  get();
  return 0;
}
int main(void) {
  pthread_t t;
  pthread_create(&t, 0, reader, 0);
  g = 4; // target: g = 4
  pthread_join(t, 0);
  return 0;
}
