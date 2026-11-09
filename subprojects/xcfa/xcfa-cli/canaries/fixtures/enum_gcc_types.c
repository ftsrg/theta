// Enumerations get GCC's types: unsigned int without negative values, int with them, and a wider
// type once a value does not fit int, which the constants then share. Holds on ILP32 and LP64.
extern void abort(void);
void reach_error() { abort(); }

enum E { A, B };
enum F { N = -1, P };
enum W { X = 0x100000000 };
enum L { LA = -1, LB = 0x80000000 };
enum G { GA = 1 };
enum H { HA, HB, HC, HD };
typedef enum { TA, TB } T;
enum { U = 0x80000000 };
enum { ONE = 1 };
enum { B1 = 1, B2 = 0x80000000 };
enum { V = 0x8000000000000000 };
enum { TEN = 1 ? 10 : 20 };
enum { N1 = -5, M1 };
enum { R1 = 2, R2 = R1 * 3, S1 = 1 << 3 };

struct S { enum H f : 2; };
enum G g;

int main() {
  enum E e = -1;
  if (!(e > 0)) reach_error();
  enum F f = -1;
  if (!(f < 0)) reach_error();
  enum W w = X;
  if (!(w == 0x100000000 && sizeof(w) == 8)) reach_error();
  enum L l = LA;
  if (!(sizeof(l) == 8 && l < 0 && LB > 0)) reach_error();
  g = -1;
  if (!(g > 0)) reach_error();
  T t = -1;
  if (!(t > 0)) reach_error();
  struct S s;
  s.f = 3;
  if (!(s.f == 3)) reach_error();
  if (!(U > 0)) reach_error();
  if (!(ONE - 2 < 0)) reach_error();
  if (!(B1 - 2 > 0)) reach_error();
  if (!(V == 0x8000000000000000)) reach_error();
  if (!(TEN == 10)) reach_error();
  if (!(M1 == -4 && R2 == 6 && S1 == 8)) reach_error();
  return 0;
}
