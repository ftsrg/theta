// PTHREAD_MUTEX_ERRORCHECK is a plain enum constant of <pthread.h> (= PTHREAD_MUTEX_ERRORCHECK_NP).
// A frontend macro mapping it to an unsupported initializer shadowed the constant, so its value
// was lost.
#include <pthread.h>
extern void abort(void);
void reach_error() { abort(); }

int main() {
  int kind = PTHREAD_MUTEX_ERRORCHECK;
  if (kind != PTHREAD_MUTEX_ERRORCHECK_NP) reach_error();
  if (kind != 2) reach_error();
  return 0;
}
