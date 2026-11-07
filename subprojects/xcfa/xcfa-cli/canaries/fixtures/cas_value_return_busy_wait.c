// Returning the value of an address-taken local does not publish its address.
#include <pthread.h>
int g;
static int cas(int *a, int e) {
  int exp = e;
  __atomic_compare_exchange_n(a, &exp, 1, 0, 5, 5);
  return exp;
}
void *run(void *arg) {
  while (cas(&g, 0) != 0) {}
  return 0;
}
int main(void) {
  pthread_t t;
  pthread_create(&t, 0, run, 0);
  g = 1;
  return 0;
}
