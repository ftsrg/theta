// The .bug twin of narrowing_signed_conversion.c: (int) of a 64-bit enum keeps the low 32 bits.
extern void abort(void);
void reach_error() { abort(); }
typedef enum { VALUE = 0x8000000000000000 } enum_t;
enum_t get(void) { return VALUE; }
int main() {
  int x = (int)get();
  enum_t y = (enum_t)x;
  if (y != VALUE) reach_error();
  return 0;
}
