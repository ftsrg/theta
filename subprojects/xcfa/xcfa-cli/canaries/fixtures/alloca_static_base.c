// Stack objects take their base from the runtime allocation counter in the *same*
// `3k+1` residue class the frontend mints compile-time bases from. The counter used
// to start at zero, so the first `alloca` was handed base 4 -- which the second
// compile-time object already owned. Two distinct C objects then shared an address
// and initialising the local silently overwrote the global.
extern void abort(void);
void reach_error() { abort(); }

struct S {
  char n[4];
  int k;
} s = {{120, 121}, 7};
char g0[4] = {1, 2, 3, 4};
char g1[4] = {5, 6, 7, 8};

int main() {
  char l0[8] = {9, 9};
  char l1[8] = {8, 8};
  if (s.n[0] != 120 || s.n[1] != 121 || s.k != 7) reach_error();
  if (g0[0] != 1 || g1[0] != 5) reach_error();
  if (l0[0] != 9 || l1[0] != 8) reach_error();
  return 0;
}
