// Planted bug: the `bool : 1` member next to `unsigned int : 1` ones really is set.
#include <stdbool.h>
extern void __assert_fail(const char *, const char *, unsigned int, const char *);
void reach_error() { __assert_fail("0", "bool_bitfield_bytes_unsafe.c", 4, "reach_error"); }
struct pm { int state; unsigned int can_wakeup : 1; unsigned int async_suspend : 1; bool is_prepared : 1; bool is_suspended : 1; };
struct pm g;
int main() { g.async_suspend = 1; g.is_prepared = 2; if (g.is_prepared && g.async_suspend && !g.can_wakeup) reach_error(); return 0; }
