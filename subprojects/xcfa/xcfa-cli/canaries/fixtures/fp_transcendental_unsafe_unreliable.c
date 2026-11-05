// An uninterpreted transcendental admits values the real function never returns, so a
// counterexample through one is not trusted: the over-approximation flag turns Unsafe into
// Unknown. Here expf(1.0f) is about 2.718, never 100, yet the model reaches the error.
extern void abort(void);
void reach_error(){ abort(); }
extern float expf(float x);

int main() {
  if (expf(1.0f) > 100.0f) reach_error();
  return 0;
}
