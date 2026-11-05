// `&a[2]` and `a + 3` are different addresses.
extern void abort(void);
void reach_error() { abort(); }

int a[4];

int main() {
  if (&a[2] != a + 3) reach_error();
  return 0;
}
