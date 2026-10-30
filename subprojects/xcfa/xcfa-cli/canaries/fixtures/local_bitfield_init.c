// Packed bitfields share a storage cell, so a local brace initializer has to splice each value
// into its own bits rather than assign the whole cell once per member.
extern void abort(void);
void reach_error() { abort(); }

struct flags { unsigned a : 3, b : 5; int c; };

int main(void) {
  struct flags lo = {6, 9, 4};
  struct flags part = {.b = 3};
  if (lo.a != 6 || lo.b != 9 || lo.c != 4) reach_error();
  if (part.a != 0 || part.b != 3 || part.c != 0) reach_error();
  return 0;
}
