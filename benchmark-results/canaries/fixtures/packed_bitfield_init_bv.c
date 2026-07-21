// batch 51: the same packed-bitfield initializer under bitvector arithmetic, where the fold uses
// Extract/Concat rather than div/mod. Word-width bitfields on purpose, so that this fixture pins
// the *initializer* fold and nothing else. (Char-width bitfields used to hit a separate,
// pre-existing "(Bv 8)" gap; that is fixed in batch 54 and guarded by char_bitfield_bitvector.c.)
struct F { unsigned x:4; unsigned y:4; unsigned rest:24; };
struct F f = {1, 2};
struct F g = {.y = 5};
int main() { return (f.x != 1) + (f.y != 2) + (g.y != 5); }
