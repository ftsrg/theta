// Assignment and comma operators in an unparenthesized array index keep their side effects and
// sequencing: `a[i = 2]` assigns `i`, `a[j++, j]` reads after the increment.
extern void abort(void);
void reach_error() { abort(); }

int main() {
  int a[3] = {0, 1, 2};
  int i = 0, j = 0;
  int v = a[i = 2];
  int w = a[j++, j];
  if (i != 2 || v != 2 || j != 1 || w != 1) reach_error();
  return 0;
}
