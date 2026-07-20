// batch 51: the same packed-bitfield initializer under bitvector arithmetic, where the fold uses
// Extract/Concat rather than div/mod. Word-width (not char-width) bitfields on purpose: an
// `unsigned char` bitfield hits a *separate, pre-existing* bitvector gap ("No suitable width
// found for type: (Bv 8)") that has nothing to do with initializers -- it fails identically with
// no initializer in sight -- so using one here would pin the wrong bug.
struct F { unsigned x:4; unsigned y:4; unsigned rest:24; };
struct F f = {1, 2};
struct F g = {.y = 5};
int main() { return (f.x != 1) + (f.y != 2) + (g.y != 5); }
