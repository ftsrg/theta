#include <pthread.h>
int g = 0;
void *reader(void *arg) {
  int n = 0;
  for (int i = 0; i < g; i++) { // target: i < g
    n++;
  }
  return 0;
}
int main(void) {
  pthread_t t;
  pthread_create(&t, 0, reader, 0);
  g = 3; // target: g = 3
  pthread_join(t, 0);
  return 0;
}
