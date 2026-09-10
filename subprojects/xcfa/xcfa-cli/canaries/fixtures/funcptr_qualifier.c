// A type qualifier after the star inside a function-pointer declarator: `void (* Q fp)(void)`. The
// star is parenthesized into the declarator (unlike `int * Q p`, whose star is at the type-specifier
// level), so its qualifier used to trip a checkState that was swallowed, silently dropping the whole
// declaration -- `fp` then did not exist ("No such variable: fp"). const/volatile/restrict are
// ignored; `_Atomic` makes the pointer variable atomic. This builds iff `fp` is registered.
void f(void) {}

void (*_Atomic afp)(void);
void (*const cfp)(void);
void (*volatile vfp)(void);

int main(void) {
  afp = f;
  cfp = f;
  vfp = f;
  return 0;
}
