// A NaN keeps its class through the integer view and back. Expected: safe.
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
  u.value = 0.0 / 0.0;
  u32 hi = u.parts.msw;
  u32 lo = u.parts.lsw;
  if ((hi & 0x7FF00000u) != 0x7FF00000u) reach_error();
  if ((hi & 0x000FFFFFu) == 0u && lo == 0u) reach_error();
  shape v;
  v.parts.msw = hi;
  v.parts.lsw = lo;
  double back = v.value;
  if (back == back) reach_error();
  return 0;
}
