// A thread writes past a one-int heap block that main allocated into a global.
#include <pthread.h>
#include <stdlib.h>
int* history;
void* teller(void* arg) {
  history[1] = 1;
  return 0;
}
int main(void) {
  history = malloc(sizeof(int));
  if (history == 0)
    return 0;
  pthread_t t;
  pthread_create(&t, 0, teller, 0);
  pthread_join(t, 0);
  free(history);
  return 0;
}
