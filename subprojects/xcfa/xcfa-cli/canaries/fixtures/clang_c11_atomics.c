// What `clang -E` makes of <stdatomic.h>: every C11 operation becomes a `__c11_atomic_*` builtin
// with the arguments of the matching `atomic_*_explicit` function (5 is memory_order_seq_cst).
// None of them has a declaration, so each failed as "No such variable or macro".
extern void abort(void);
void reach_error(){ abort(); }

typedef _Atomic(_Bool) atomic_bool;
typedef _Atomic(long) atomic_long;
typedef struct atomic_flag { atomic_bool _Value; } atomic_flag;

atomic_long x;
atomic_flag flag;

int main(void) {
  long expected = 3;

  __c11_atomic_init(&x, 0);
  __c11_atomic_store(&x, 1, 5);
  if (__c11_atomic_load(&x, 5) != 1) reach_error();

  if (__c11_atomic_exchange(&x, 2, 5) != 1) reach_error();
  if (__c11_atomic_fetch_add(&x, 1, 5) != 2) reach_error();

  /* x is 3: the exchange succeeds, and a second one then fails and loads the current value */
  if (!__c11_atomic_compare_exchange_strong(&x, &expected, 7, 5, 5)) reach_error();
  if (__c11_atomic_compare_exchange_weak(&x, &expected, 9, 5, 5)) reach_error();
  if (expected != 7) reach_error();
  __c11_atomic_thread_fence(5);

  /* atomic_flag_test_and_set and atomic_flag_clear */
  if (__c11_atomic_exchange(&(&flag)->_Value, 1, 5)) reach_error();
  if (!__c11_atomic_exchange(&(&flag)->_Value, 1, 5)) reach_error();
  __c11_atomic_store(&(&flag)->_Value, 0, 5);
  if (__c11_atomic_load(&flag._Value, 5)) reach_error();

  return 0;
}
