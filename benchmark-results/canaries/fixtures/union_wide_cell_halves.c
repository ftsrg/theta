// batch 92 item 9, the ILP32 half: a union whose cell is 64 bits wide.
//
// The cell was read as `unsigned long`, which is 64 bits only under LP64 -- under ILP32 it is 32,
// so `union { long long QuadPart; struct { unsigned int LowPart; int HighPart; }; }` was read at
// HALF its width and `HighPart` (bit 32) then spliced past the cell's end, producing a 64-bit
// value for a 32-bit cell. That is ntdrivers' `_LARGE_INTEGER` and the ldv-linux drivers'
// descriptor unions -- 174 of the 298 runs. All widths here are the same in both data models,
// so the expected values do not depend on the architecture; only theta's cell choice did.
extern void abort(void);
void reach_error() { abort(); }

typedef union {
  struct {
    unsigned int LowPart;
    int HighPart;
  };
  long long QuadPart;
} large_t;

int main() {
  large_t x;
  x.QuadPart = 0;
  x.LowPart = 7u;
  x.HighPart = 3;
  if (x.QuadPart != (((long long)3 << 32) + 7)) reach_error();
  x.QuadPart = ((long long)5 << 32) + 9;
  if (x.LowPart != 9u || x.HighPart != 5) reach_error();
  x.HighPart = -1;
  if (x.LowPart != 9u) reach_error();
  return 0;
}
