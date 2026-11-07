// The difference of two pointers converted to integers is an offset, not an address: with a
// `free` in the program, it still does not make a Safe verdict unreliable.
#include <stdlib.h>

long length(const char *str) {
  const char *s = str;
  while (*s) s++;
  return (long)s - (long)str;
}

int main(void) {
  char *p = malloc(4);
  if (p == 0) return 0;
  p[0] = 'a';
  p[1] = 0;
  long n = length(p);
  free(p);
  return n == 1 ? 0 : 1;
}
