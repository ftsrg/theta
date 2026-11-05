// An overflow behind a spinning acquire must be found when the overflow chain reaches OC under multi.
#include <pthread.h>
int lock;
int counter = 2147483647;
void *worker(void *arg) {
  int expected = 0;
  while (!__atomic_compare_exchange_n(&lock, &expected, 1, 0, 5, 5)) {
    expected = 0;
  }
  counter++;
  __atomic_store_n(&lock, 0, 5);
  return 0;
}
int main(void) {
  pthread_t t;
  pthread_create(&t, 0, worker, 0);
  worker(0);
  pthread_join(t, 0);
  return 0;
}
