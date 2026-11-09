// gcc on x86 keeps a NaN payload through a double copy, so this is safe. SMT-LIB has a single NaN,
// so Theta cannot know the payload: it must not answer unsafe.
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
  u.parts.msw = 0x7FF80000u;
  u.parts.lsw = 42u;
  double d = u.value;
  u.value = d;
  if (u.parts.lsw != 42u) reach_error();
  return 0;
}
