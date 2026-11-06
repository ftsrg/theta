// One branch can never be taken, because the value it tests is always 0, so its local has no value.
// The error lies behind the merge: the condition of the dead path must not end the live one.
#include <pthread.h>
extern void abort(void);
void reach_error() {
  abort();
}
struct cell {
  int zero;
  int value;
};
struct cell c;
void* writer(void* arg) {
  c.value = 1;
  return 0;
}
int main(void) {
  pthread_t t;
  int v = 0;
  pthread_create(&t, 0, writer, 0);
  int zero = c.zero;
  if (zero == 1) {
    int local = c.value;
    if (local == 3)
      v = 1;
  } else {
    v = 2;
  }
  pthread_join(t, 0);
  if (v == 2)
    reach_error();
  return 0;
}
