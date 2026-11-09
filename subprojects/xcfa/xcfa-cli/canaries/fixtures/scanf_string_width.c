// `%9s` stores at most nine characters and the terminating 0: the buffer holds them.
#include <stdio.h>

int main(void) {
  char buf[10];
  char *p = buf;
  if (scanf("%9s", p) == 1) {
    return buf[0];
  }
  return 0;
}
