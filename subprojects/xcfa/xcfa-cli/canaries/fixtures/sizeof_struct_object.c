// sizeof of a struct or union is its C size: array members count every element, and padding is
// included. Sizes are for ILP32, where a double is 4-byte aligned.
extern void abort(void);
void reach_error() { abort(); }

struct S { int a[10]; int b; };
struct T { struct S s; int c[3]; };
struct P { char c; int a[2]; };
union U { char c[5]; int i; };
struct B { unsigned a : 4; unsigned b : 4; };
struct F { char c; int d[]; };
struct Q { char c; double d; };

struct S global;
struct S elements[3];

int main() {
  struct S local;
  if (sizeof(struct S) != 44 || sizeof(global) != 44 || sizeof local != 44) reach_error();
  if (sizeof(struct T) != 56) reach_error();
  if (sizeof(struct P) != 12) reach_error();
  if (sizeof(union U) != 8) reach_error();
  if (sizeof(struct B) != 4) reach_error();
  if (sizeof(struct F) != 4) reach_error();
  if (sizeof(struct Q) != 12) reach_error();
  if (sizeof(elements) != 132 || sizeof(elements) / sizeof(elements[0]) != 3) reach_error();
  return 0;
}
