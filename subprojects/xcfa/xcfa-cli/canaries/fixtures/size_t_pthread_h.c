// `size_t` from the <pthread.h> model is `unsigned long`, so it is 64 bits wide on LP64 like the
// one from <stdlib.h>.
#include <pthread.h>
#include <stdlib.h>
extern void reach_error(void);

int main(void) {
  if (sizeof(size_t) != 8) reach_error();
  size_t s = sizeof(int) * 1073741824;
  if (s == 0) reach_error();
  return 0;
}
