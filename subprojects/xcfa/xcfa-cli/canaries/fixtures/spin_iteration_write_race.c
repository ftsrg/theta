// The racy access is a non-atomic write in a spinning iteration that restores what it read: it has
// no effect on the state, but it still races with the other thread's write.
#include <pthread.h>
int flag;
int shared;
void *spinner(void *arg) {
  while (__atomic_load_n(&flag, 5) == 0) {
    shared = shared;
  }
  return 0;
}
void *writer(void *arg) {
  shared = 1;
  __atomic_store_n(&flag, 1, 5);
  return 0;
}
int main(void) {
  pthread_t a, b;
  pthread_create(&a, 0, spinner, 0);
  pthread_create(&b, 0, writer, 0);
  pthread_join(a, 0);
  pthread_join(b, 0);
  return 0;
}
