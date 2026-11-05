// atoi skips white space, reads a sign and stops at the first non-digit.
extern void abort(void);
void reach_error() { abort(); }
extern int atoi(const char *s);

int main() {
  if (atoi(" -12x") != -12) reach_error();
  if (atoi("+7") != 7) reach_error();
  if (atoi("x1") != 0) reach_error();
  return 0;
}
