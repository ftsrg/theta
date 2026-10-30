// strcmp is analysed through its C model, not stubbed: two different strings never compare equal.
extern void abort(void);
void reach_error() { abort(); }
extern int strcmp(const char *, const char *);

int main() {
  char a[2] = "a";
  char b[2] = "b";
  if (!strcmp(a, b)) reach_error();
  return 0;
}
