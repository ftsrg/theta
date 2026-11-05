// A stored mid-object pointer is refused under multi: the flat check has to find its object, also
// when the dereference is a branch condition.
#include <pthread.h>
struct node {
  int key;
  int cells[2];
};
struct node nodes[2];
int *volatile slot;
void *worker(void *arg) {
  int *p = slot;
  if (p && p[2]) nodes[0].key = 1;
  return 0;
}
int main(void) {
  pthread_t t;
  slot = &nodes[1].cells[0];
  pthread_create(&t, 0, worker, 0);
  pthread_join(t, 0);
  return 0;
}
