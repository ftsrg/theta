#include <stdlib.h>

int main(void) {
  int *p = malloc(2);
  free(p);
  return 0;
}
