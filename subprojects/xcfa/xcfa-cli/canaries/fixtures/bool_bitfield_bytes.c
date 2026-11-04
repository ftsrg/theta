// Mixed `unsigned int : 1` / `bool : 1` bitfields (the Linux `dev_pm_info` shape): a `_Bool`
// bitfield is stored in a byte, so it never straddles its unit under the bytes model.
#include <stdbool.h>
extern void __assert_fail(const char *, const char *, unsigned int, const char *);
void reach_error() { __assert_fail("0", "bool_bitfield_bytes.c", 3, "reach_error"); }
struct pm { int state; unsigned int can_wakeup : 1; unsigned int async_suspend : 1; bool is_prepared : 1; bool is_suspended : 1; };
struct pm g = { 0, 1, 0, 2, 0 };
int main() { g.is_suspended = 4; g.async_suspend = 1; if (!g.is_prepared || !g.is_suspended || !g.can_wakeup || !g.async_suspend || g.state != 0) reach_error(); return 0; }
