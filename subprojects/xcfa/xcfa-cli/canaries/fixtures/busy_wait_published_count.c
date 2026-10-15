// a busy-wait loop whose local count is published to a global must not be collapsed
#include <pthread.h>
extern void reach_error(void);
int flag = 0;
int g = 0;
void *setter(void *arg) { flag = 1; return 0; }
void *spinner(void *arg) {
  int x = 0;
  while (flag == 0) { x = x + 1; }
  g = x;
  return 0;
}
int main(void) {
  pthread_t a, b;
  pthread_create(&b, 0, spinner, 0);
  pthread_create(&a, 0, setter, 0);
  pthread_join(a, 0);
  pthread_join(b, 0);
  if (g >= 2) reach_error();
  return 0;
}
