// C99 hexadecimal floating constants (`0x1.4p+4`) were refused outright, which killed the
// whole frontend on any file that used one -- 134 benchmark files contain them (104 in
// coreutils-v8.31 alone), and every one of a 30-file sample failed to parse. Java's own
// literal syntax is the same and `Double.parseDouble` reads it exactly, so the value is
// stated, not approximated -- which is what the equalities below pin down.
// `long double` keeps the refusal: its significand is wider than a double's.
extern void abort(void);
void reach_error(){ abort(); }
int main() {
  double a = 0x1.4p+4;      /* 20.0 */
  double b = 0x1p-1;        /* 0.5  */
  float  c = 0x1.8p+1f;     /* 3.0  */
  double d = 0x2.8p+3;      /* 20.0 */
  if (a != 20.0) reach_error();
  if (b != 0.5) reach_error();
  if (c != 3.0f) reach_error();
  if (d != a) reach_error();
  return 0;
}
