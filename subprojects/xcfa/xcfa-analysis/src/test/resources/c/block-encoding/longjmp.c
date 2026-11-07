// longjmp stays an unresolved call: removing it would remove the jump back to setjmp.
extern int __VERIFIER_nondet_int(void);
extern void abort(void);
void reach_error() { abort(); }
void __VERIFIER_assert(int cond) { if (!cond) { reach_error(); } }
void assume_abort_if_not(int cond) { if (!cond) { abort(); } }
int a, b, c, last;
typedef void* jmp_buf;
extern int setjmp(jmp_buf env);
extern void longjmp(jmp_buf env, int val);
jmp_buf buf;

int main() {
  volatile int count = 0;
  setjmp(buf);
  __VERIFIER_assert(count == 0);
  if (count < 5) { count++; longjmp(buf, 1); }
}
