// batch 45: consecutive bitfields pack into one storage unit and each access slices its own bits
struct A { unsigned char a; unsigned char b:2; unsigned char c:2; unsigned char d:4; };
int main() {
  struct A x; x.a = 1; x.b = 2; x.c = 3; x.d = 4;
  return (x.a != 1) + (x.b != 2) + (x.c != 3) + (x.d != 4);
}
