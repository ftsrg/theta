// `memcpy`/`memset` converted the byte count into a cell count by dividing by an element
// width. But a cell is one *member*, whatever its C width -- a struct of four `unsigned
// char` is four cells in four bytes -- and the guard meant to refuse a struct pointee never
// fired, because CStruct/CArray/CPointer all extend CInteger in this type hierarchy. So
// `memcpy(p, &d, 4)` resolved its element to the *struct*, whose width() is 32, and copied
// 4/4 = 1 cell, leaving three of the destination's four cells holding whatever they held
// before -- with no warning (ldv-memsafety-bitfields/test-bitfields-2-2).
extern void abort(void);
extern void *memcpy(void *, const void *, unsigned int);
extern void *memset(void *, int, unsigned int);
extern void *malloc(unsigned int);
void reach_error() { abort(); }

struct A {
  unsigned char a, b, c, e;
};
struct A d = {1, 2, 3, 5};

int main(void) {
  struct A *p = malloc(4);
  if (!p) return 0;
  memcpy(p, &d, 4);
  if (p->a != 1 || p->b != 2 || p->c != 3 || p->e != 5) reach_error();
  memset(p, 0, 4);
  if (p->a != 0 || p->b != 0 || p->c != 0 || p->e != 0) reach_error();
  return 0;
}
