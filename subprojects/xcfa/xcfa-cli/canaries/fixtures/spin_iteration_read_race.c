// The only racy access is a read inside an otherwise effect-free spinning iteration. Dropping that
// iteration as a useless spin must not hide the race with the writer.
#include <pthread.h>
int flag;
int shared;
void* spinner(void* arg) {
  int seen;
  while (__atomic_load_n(&flag, 5) == 0) {
    seen = shared;
  }
  return 0;
}
void* writer(void* arg) {
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
