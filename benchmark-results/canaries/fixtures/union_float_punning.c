// batch 58: floating-point union punning -- reading/writing a double's raw IEEE-754 bit pattern
// through an aliased integer view. This is the float-newlib idiom (~265 tasks); it used to be
// rejected ("members do not all share a representation") because a double's SMT sort is not a
// bitvector. FpToIeeeBv / FpFromIeeeBv are the reinterpretation. A float forces bitvector
// arithmetic, so the shared cell is a bitvector. Value semantics (1.0 <-> msw 0x3FF00000) are
// checked end to end by the module tests; this fixture guards that the shapes reach the frontend.
typedef unsigned int u32;

typedef union {
  double value;
  struct {
    u32 lsw;
    u32 msw;
  } parts;
} shape;

typedef union {
  double value;
  unsigned long bits;
} scalar_shape;

shape a;
scalar_shape b;

int main() {
  a.value = 1.0;
  u32 hi = a.parts.msw; // read the high word out of the double's encoding
  a.parts.msw = 0x40000000u; // write the halves ...
  a.parts.lsw = 0u;
  double back = a.value; // ... and read the double back
  b.value = 2.0;
  unsigned long raw = b.bits;
  return (hi == 0) + (back == 0.0) + (raw == 0);
}
