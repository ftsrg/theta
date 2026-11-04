// A spin lock is modeled as a mutex, so the increments do not interleave.
#include <pthread.h>
extern void abort(void);
void reach_error() { abort(); }
pthread_spinlock_t l;
int x;
void *w(void *a) { pthread_spin_lock(&l); x++; pthread_spin_unlock(&l); return 0; }
int main() {
  pthread_t t;
  pthread_spin_init(&l, 0);
  pthread_create(&t, 0, w, 0);
  pthread_spin_lock(&l); x++; pthread_spin_unlock(&l);
  pthread_join(t, 0);
  if (x != 2) reach_error();
  return 0;
}
