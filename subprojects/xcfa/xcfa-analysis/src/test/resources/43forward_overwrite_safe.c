// The second write to the same cell executes whenever the read does: the first is overwritten.
extern void reach_error(void);

int a[4];

int main(void) {
  int *p = &a[1];
  *p = 1;
  *p = 2;
  if (a[1] == 1) reach_error();
  return 0;
}
