// batch 51: a brace initializer on a struct whose bitfields pack.
// Elements index *members*, storage is per *unit*, so `{1, 2}` folds into one cell (0x21) and
// `.b = 3` splices into its own bits. Batch 45 refused this outright, which cost 36 benchmark
// tasks (30 ldv-linux-3.4-simple, 5 ldv-memsafety-bitfields, 1 ldv-challenges) -- the shape
// below is exactly ldv-memsafety-bitfields/test-bitfields-3-1.
struct A { unsigned char a; unsigned char b:2; unsigned char c:2; unsigned char d:4; };
struct A d = {.b = 3};
struct A e = {1, 2, 3, 4};
struct F { unsigned x:4; unsigned y:4; };
struct F f = {1, 2};
int main() {
  return (d.b != 3) + (e.a != 1) + (e.b != 2) + (e.d != 4) + (f.x != 1) + (f.y != 2);
}
