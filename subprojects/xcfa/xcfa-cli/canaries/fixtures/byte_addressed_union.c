// batch 60 (AD7, the intractable half): a union whose members do not all share a representation
// AND cannot be packed into one word (unionCellWidth() == null -- an array member disqualifies it)
// used to be refused outright as "members do not all share a representation". This is the
// intel-tdx-module shape: `union { uint64_t qwords[2]; uint32_t dwords[4]; uint8_t bytes[16]; }`
// has no single word for a sibling to slice, so it needs real byte-addressed cells instead.
// Semantics are checked end to end elsewhere (little-endian recombination, a variable index, the
// deliberate refusals for a bitfield/float/nested-aggregate member and for &-of a multi-byte
// member); this fixture only guards that the shape still reaches the frontend at all.
typedef union {
  unsigned long qwords[2];
  unsigned int dwords[4];
  unsigned char bytes[16];
} uint128_t;

union Mixed {
  unsigned long raw;
  unsigned char bytes[8];
};

uint128_t u;
union Mixed m;

int main() {
  int i = 3;
  u.qwords[0] = 0x0102030405060708UL;
  u.qwords[1] = 0;
  m.raw = 0x0102030405060708UL;
  unsigned char *p = &u.bytes[0];
  return (u.bytes[0] != 0x08) + (u.dwords[0] != 0x05060708) + (m.bytes[i] == 0 ? 0 : 0) + (*p == 0 ? 0 : 0);
}
