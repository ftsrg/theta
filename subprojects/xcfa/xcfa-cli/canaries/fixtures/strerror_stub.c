// strerror only reads its argument: its result going to a printf must not stop the analysis.
#include <pthread.h>
#include <stdio.h>
#include <string.h>
extern void reach_error(void);
int shared;
void *worker(void *arg) {
  int status = shared;
  if (status != 0) fprintf(stderr, "%s\n", strerror(status));
  return 0;
}
int main(void) {
  pthread_t t;
  pthread_create(&t, 0, worker, 0);
  pthread_join(t, 0);
  if (shared != 0) reach_error();
  return 0;
}
