// The deref in the condition follows a null check on both branch edges. Both edges must read the
// same value of c.value, or one execution takes both branches and reports a false alarm.
#include <pthread.h>
extern void abort(void);
void reach_error() {
  abort();
}
struct cell {
  int padding;
  int value;
};
struct cell c;
int taken_then, taken_else;
void* writer(void* arg) {
  c.value = 1;
  return 0;
}
void branch(struct cell* p) {
  if (p->value == 0)
    taken_then = 1;
  else
    taken_else = 1;
}
int main(void) {
  pthread_t t;
  pthread_create(&t, 0, writer, 0);
  branch(&c);
  pthread_join(t, 0);
  if (taken_then && taken_else)
    reach_error();
  return 0;
}
