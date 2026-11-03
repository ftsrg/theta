#include <pthread.h>
int g = 0;
void *writer(void *arg) {
  g = 1; // target: g = 1
  return 0;
}
void *busy(void *arg) {
  int local = 0;
  for (int i = 0; i < 3; i++) {
    local = local + i;
  }
  return 0;
}
int main(void) {
  pthread_t a, b;
  pthread_create(&b, 0, busy, 0);
  pthread_create(&a, 0, writer, 0);
  int v = g + 2; // target: g + 2
  pthread_join(a, 0);
  pthread_join(b, 0);
  return v;
}
