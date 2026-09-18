// The other side: a block-local array used entirely inside its own block is live
// throughout, and the scope-end release must not invent a violation. Covers a bare block, a
// loop body (released once per iteration) and an if-arm.
extern void abort(void);
void reach_error() { abort(); }

int main() {
  int t = 0;
  {
    int a[4];
    for (int i = 0; i < 4; i++) a[i] = i;
    t += a[3];
  }
  for (int i = 0; i < 3; i++) {
    int b[2];
    b[0] = i;
    t += b[0]; // used within the same iteration
  }
  if (t > 0) {
    int c[2];
    c[0] = 5;
    t += c[0];
  }
  if (t != 3 + 5 + 3) reach_error();
  return 0;
}
