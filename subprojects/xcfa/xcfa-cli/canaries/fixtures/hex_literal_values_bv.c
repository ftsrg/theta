// Hex constants take the first type of int, unsigned int, long, unsigned long, ... that holds
// their value (C11 6.4.4.1p5), and a bitvector literal is built with that type's width and sign.
extern void abort(void);
void reach_error() { abort(); }
int main() {
  long big = 0x100000000;
  if (big != 4294967296L) reach_error();
  if (sizeof(0x100000000) != 8) reach_error();
  if (0x80000000 < 0) reach_error();
  long masked = -1L & 0xffffffff;
  if (masked != 4294967295L) reach_error();
  return 0;
}
