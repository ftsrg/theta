// An exit handler runs after main returns; registering one without running it is refused.
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *);
void reach_error() { __assert_fail("0", "atexit_handler_refused.c", 3, "reach_error"); }
extern int atexit(void (*func)(void));

void handler(void) { reach_error(); }

int main() {
  if (atexit(handler)) abort();
  return 0;
}
