// A char view of an int object addresses its bytes: `c[1]` is byte 1 of the first int, not the
// second int. The cell models cannot express that, so the cast is refused there and the default
// configuration falls back to the bytes model.
extern void abort(void);
void reach_error(void) { abort(); }
int g[3];
int main(void) {
  char *c = (char *)g;
  c[1] = 1;
  if (g[1] != 0) reach_error();
  return 0;
}
