#include <pthread.h>
int shared;
pthread_mutex_t mutex = PTHREAD_MUTEX_INITIALIZER;
void *reader(void *arg) {
  pthread_mutex_lock(&mutex);
  shared = 1;
  pthread_mutex_unlock(&mutex);
  return 0;
}
void *helper(void *arg) { return 0; }
int main(void) {
  pthread_t r, h;
  pthread_create(&r, 0, reader, 0);
  pthread_create(&h, 0, helper, 0);
  pthread_join(h, 0);
  shared = 2;
  pthread_join(r, 0);
  return 0;
}
