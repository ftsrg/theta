// `fgets` may store up to `n` characters; a size above the exact model's limit still checks them.
#include <stdio.h>

int main(void) {
  char buf[10];
  if (fgets(buf, 300, stdin) == NULL) return 0;
  return buf[0];
}
