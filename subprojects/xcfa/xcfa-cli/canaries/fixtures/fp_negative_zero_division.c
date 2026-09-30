// 1.0f / -0.0f is -inf. The sign of a floating-point zero literal was read inverted when folding
// constants, so the division came out +inf and the error was reported unreachable.
extern void abort(void);
void reach_error() { abort(); }
int main(void) {
  float z = -0.0f;
  float r = 1.0f / z;
  if (r < 0.0f) reach_error();
  return 0;
}
