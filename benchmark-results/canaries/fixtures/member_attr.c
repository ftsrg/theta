// batch 39: __attribute__ between specifier and struct member declarator + bitfield attrs
struct A {
  int __attribute__((aligned(4))) x;
  unsigned lo : 4 __attribute__((deprecated));
  int y;
};
int main() { struct A a; a.x = 1; a.y = 2; return (a.x != 1) + (a.y != 2); }
