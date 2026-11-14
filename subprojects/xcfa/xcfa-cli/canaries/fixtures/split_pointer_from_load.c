// A pointer that gets stepped is split into a base and an offset under multi. Assigning it a
// pointer loaded from memory, or a null constant behind casts, starts it at offset 0.
extern void abort(void);
void reach_error() {}
struct inner { int v[2]; };
struct outer { struct inner *n; int k; };
struct inner I;
struct outer O;
int main() {
  int *q = (void *)0;
  O.n = &I;
  I.v[1] = 7;
  q = O.n->v;
  q = q + 1;
  if (*q != 7) { reach_error(); abort(); }
  return 0;
}
