// A static object is not an allocation: nothing here needs releasing. On bitvectors a heap base
// computed by multiplying with the class count wraps onto the object's address.
#include <pthread.h>
int x;
void* worker(void* arg) {
  int* p = &x;
  *p = 1;
  return 0;
}
int main(void) {
  pthread_t t;
  pthread_create(&t, 0, worker, 0);
  pthread_join(t, 0);
  return 0;
}
