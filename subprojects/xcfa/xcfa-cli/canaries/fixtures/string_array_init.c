// `char s[N] = "lit"` is an aggregate initializer written without braces. A string
// literal folds to the opaque `int(1)`, so the declaration used to emit `s = 1`:
// the array's own base was clobbered by a bare integer, no cell was ever written,
// and `s` aliased whatever object happened to have base id 1 -- which is how a local,
// an unrelated global with an equal literal, and the bare literal all collapsed onto
// one object.
extern void abort(void);
void reach_error() { abort(); }

char g[8] = "ab";

int main() {
  char l[8] = "ab";
  char exact[2] = "ab"; // no room for the terminator: C stores just the two chars
  if (g[0] != 'a' || g[1] != 'b' || g[2] != 0 || g[7] != 0) reach_error();
  if (l[0] != 'a' || l[1] != 'b' || l[2] != 0 || l[7] != 0) reach_error();
  if (exact[0] != 'a' || exact[1] != 'b') reach_error();
  l[0] = 'Z'; // a local array initialised from a literal is its own mutable object
  if (g[0] != 'a') reach_error();
  return 0;
}
