// The unit with main. `counter` and `step` are its own; `shared` and `from_b` are not.
void reach_error(void);
extern int shared;
int from_b(void);
__attribute__((weak)) int helper(void) { return 7; }
struct Pair { int a; int b; };
static int counter = 1;
static int step(void) { return counter += 2; }
int main(void) {
  struct Pair p = {1, 2};
  shared += step() + p.a;
  if (from_b() != shared + 100) reach_error();
  return helper() == 7 ? 0 : 1;
}
