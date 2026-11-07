// Planted bug: the high word of 1.0 is 0x3FF00000. Expected: unsafe.
extern void abort(void);
void reach_error() { abort(); }
typedef unsigned int u32;
typedef union {
  double value;
  struct {
    u32 lsw;
    u32 msw;
  } parts;
} shape;

int main() {
  shape u;
  u.value = 1.0;
  if (u.parts.msw == 0x3FF00000u) reach_error();
  return 0;
}
