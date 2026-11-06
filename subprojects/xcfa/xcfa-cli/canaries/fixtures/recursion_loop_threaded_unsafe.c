// As recursion_loop_threaded_safe.c, with a bug only the full recursion depth reaches.
#include <pthread.h>
extern void reach_error(void);
int cells[3];
int next;
void fill(int depth) {
  if (depth == 2)
    return;
  for (int i = 0; i < 2; i++) {
    if (next < 3)
      cells[next++] = 1;
    fill(depth + 1);
  }
}
void* worker(void* arg) {
  return 0;
}
int main(void) {
  pthread_t t;
  fill(0);
  pthread_create(&t, 0, worker, 0);
  pthread_join(t, 0);
  if (cells[2] == 1)
    reach_error();
  return 0;
}
