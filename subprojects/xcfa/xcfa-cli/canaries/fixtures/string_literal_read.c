// A string literal whose characters are read keeps its initialization: dropping the
// per-character init of a literal nothing reads must not touch one that is read.
extern void abort(void);
void reach_error() { abort(); }
int main(void) {
  const char *s = "AB";
  if (s[0] != 'A' || s[1] != 'B' || s[2] != 0) reach_error();
  return 0;
}
