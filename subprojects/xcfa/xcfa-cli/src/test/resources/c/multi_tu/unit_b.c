// No main here. The same names as in unit_a, as objects of this unit, and the same tag with
// other members; a constructor, as only unit_a can reach it through main.
int shared = 40;
__attribute__((weak)) int helper(void) { return 7; }
struct Pair { long x; };
static int counter = 100;
static int step(void) { return counter++; }
__attribute__((constructor)) static void setup(void) { shared += 2; }
int from_b(void) {
  struct Pair p = {step()};
  return shared + (int)p.x;
}
