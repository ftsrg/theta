#include <pthread.h>
int g = 0;
void *reader(void *arg) {
  if (g > 0) { // target: g > 0
    return 0;
  }
  return 0;
}
int main(void) {
  pthread_t t;
  pthread_create(&t, 0, reader, 0);
  g = 1; // target: g = 1
  pthread_join(t, 0);
  return 0;
}
