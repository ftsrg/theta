// && and || combine the values their operands had when evaluated: an effect of a later operand
// used to change what an earlier one read, so `(x == 1) && (--x == 0)` came out false.
extern void abort(void);
void reach_error() { abort(); }

int g = 0;
int set_g(void) { g = 1; return 1; }

int main() {
  int x = 1;
  int b = (x == 1) && (--x == 0);
  if (!b) reach_error();

  b = (g == 0) && set_g();
  if (!b) reach_error();

  x = 0;
  b = (x == 1) || x++;
  if (b || x != 1) reach_error();
  return 0;
}
