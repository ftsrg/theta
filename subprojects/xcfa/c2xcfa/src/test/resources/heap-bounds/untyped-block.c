#include <stdlib.h>

int main(void) {
  void *v = malloc(8);
  if (v) ((int *)v)[1] = 1;
  return 0;
}
