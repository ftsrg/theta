// `bool`, `true` and `false` come from <stdbool.h>, which un-preprocessed tasks may include.
#include <stdbool.h>
extern void reach_error(void);
bool flag = true;

int main(void) {
  bool off = false;
  if (!flag || off) reach_error();
  if (true != 1 || false != 0) reach_error();
  return 0;
}
