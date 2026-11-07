// `%s` without a width stores a whole input word, which may be longer than the buffer.
#include <stdio.h>

int main(void) {
  char buf[10];
  if (scanf("%s", buf) == 1) {
    return buf[0];
  }
  return 0;
}
