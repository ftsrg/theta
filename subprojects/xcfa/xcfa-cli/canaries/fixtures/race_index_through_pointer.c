// The thread's index is read through a pointer, so its racing write is to a[(deref ...)], whose
// offset has no variable for the points-to analysis to resolve. SPOR must treat it as unknown (and
// the write as dependent on main's a[1] = 1); treated as resolved to nothing, the race was missed.
#include <pthread.h>
int a[2];
int idx = 0;
int *pidx = &idx;
void *thr(void *arg) {
  *pidx = 1;
  a[*pidx] = 2;
  return 0;
}
int main() {
  pthread_t id;
  pthread_create(&id, 0, thr, 0);
  a[1] = 1;
  pthread_join(id, 0);
  return 0;
}
